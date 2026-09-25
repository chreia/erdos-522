/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HarmonicRestriction
import Erdos522.Limits.RealPowerBlocks
import Erdos522.Probability.SparseLogarithmicConcentration
import Erdos522.Probability.AnnularSmallDerivativeAlmostSure
import Erdos522.Probability.TailSupremum

/-!
# Concentration along rounded real-power degrees

The finite logarithmic and annular estimates have summable exceptional
probabilities along `⌊j^q⌋` whenever `q > 8/3`. The maximal appended-tail
estimate is summable for every `q > 1` and covers the entire degree block.
All events are realized by prefixes of the same infinite sign sequence.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Erdos522
open LogMoments

/-- The actual logarithmic failures are summable along every rounded real-power
schedule above `8/3`, for any fixed finite family of radii. -/
theorem summable_real_power_radialLogarithmicFailure {q : ℝ} (hq : 8 / 3 < q)
    {ι : Type*} [Fintype ι] (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N) :
    Summable (fun j : ℕ => (signMeasure (realPowerDegree q j)).real
      (radialLogarithmicFailure (realPowerDegree q j) (r (realPowerDegree q j)))) := by
  obtain ⟨B, _, hbound⟩ := eventually_radialLogarithmicFailure_le
    one_le_harmonicRestrictionConstant harmonic_l2_restriction K hK r hr
  have hq0 : 0 < q := by linarith
  have hsum := (summable_realPowerDegree_rpow hq0
    (show q * (-3 / 8 : ℝ) < -1 by linarith)).mul_left
      ((Fintype.card ι : ℝ) * (2 * rademacherOccupationConstant B K + 1))
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_realPowerDegree hq0).eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

/-- Almost-sure logarithmic concentration on a rounded real-power schedule. -/
theorem ae_eventually_real_power_radial_logarithmic_bound {q : ℝ} (hq : 8 / 3 < q)
    {ι : Type*} [Fintype ι] (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i,
      |logCircleAverage (rademacherPolynomial (realPowerDegree q j)
          (rademacherPrefix (realPowerDegree q j) ω)) (r (realPowerDegree q j) i) -
        Real.log (radialSigma (realPowerDegree q j) (r (realPowerDegree q j) i)) -
          circularLogMean| ≤ logarithmicTolerance (realPowerDegree q j) := by
  have h := ae_eventually_rademacherPrefix_notMem (realPowerDegree q)
    (fun N => radialLogarithmicFailure N (r N))
    (summable_real_power_radialLogarithmicFailure hq K hK r hr)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro i
  exact le_of_not_gt (fun hlarge => hj ⟨i, hlarge⟩)

/-- The complete annular failure envelope is summable on each admissible schedule. -/
theorem summable_real_power_annular_failure_envelope {q : ℝ} (hq : 8 / 3 < q) (C : ℝ) :
    Summable (fun j : ℕ => 1 / (realPowerDegree q j : ℝ) ^ 3 +
      1 / (realPowerDegree q j : ℝ) ^ 10 +
        C * (realPowerDegree q j : ℝ) ^ (-3 / 8 : ℝ) *
          (Real.log (realPowerDegree q j)) ^ 4) := by
  have hq0 : 0 < q := by linarith
  have h₁ := summable_realPowerDegree_rpow hq0 (show q * (-3 : ℝ) < -1 by linarith)
  have h₂ := summable_realPowerDegree_rpow hq0 (show q * (-10 : ℝ) < -1 by linarith)
  have h₃ := (summable_realPowerDegree_rpow_mul_log_pow hq0
    (show q * (-3 / 8 : ℝ) < -1 by linarith) 4).mul_left C
  apply (h₁.add h₂ |>.add h₃).congr
  intro j
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
  norm_num only [Real.rpow_ofNat]
  ring

/-- The multiplicity-counted annular small-derivative failures obey the same
`q > 8/3` summability threshold. -/
theorem summable_real_power_annular_small_derivative_failures {q : ℝ} (hq : 8 / 3 < q)
    (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ => (signMeasure (realPowerDegree q j)).real {ω |
      (realPowerDegree q j : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount
          (rademacherPolynomial (realPowerDegree q j) ω) (realPowerDegree q j) K
            ((realPowerDegree q j : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}) := by
  obtain ⟨C, _, hbound⟩ := eventually_annular_small_derivative_probability K (K + 2) hK le_rfl
  apply (summable_real_power_annular_failure_envelope hq C).of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_realPowerDegree (show 0 < q by linarith)).eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

/-- Almost-sure annular derivative nondegeneracy, with the finite-degree cutoff
and root-count exponent unchanged. -/
theorem ae_eventually_real_power_annular_small_derivative_count {q : ℝ} (hq : 8 / 3 < q)
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
          (realPowerDegree q j) K ((realPowerDegree q j : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤
            (realPowerDegree q j : ℝ) ^ (31 / 32 : ℝ) := by
  have h := ae_eventually_rademacherPrefix_notMem (realPowerDegree q)
    (fun N => {v | (N : ℝ) ^ (31 / 32 : ℝ) <
      (annularSmallDerivativeZeroCount (rademacherPolynomial N v) N K
        ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)})
    (summable_real_power_annular_small_derivative_failures hq K hK)
  filter_upwards [h] with ω hω
  exact hω.mono (fun _ hj => le_of_not_gt hj)

/-- Maximal appended-tail failures are summable over real-power degree blocks. -/
theorem summable_real_power_tail_failures {q : ℝ} (hq : 1 < q) (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ =>
      (signMeasure (realPowerDegree q j + realPowerBlockLength q j)).real {v |
        ∃ m : ℕ, m ≤ realPowerBlockLength q j ∧ ∃ z : ℂ,
          ‖z‖ ≤ 1 + K / realPowerDegree q j ∧
          TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) K ≤
            ‖(TailSupremum.appendedTailPolynomial
              (realPowerDegree q j) (realPowerBlockLength q j) m v).eval z‖}) := by
  have hq0 : 0 < q := by linarith
  have hsum : Summable (fun j : ℕ => 1 / (realPowerDegree q j : ℝ) ^ 10) := by
    convert summable_realPowerDegree_rpow hq0 (show q * (-10 : ℝ) < -1 by linarith) using 1
    ext j
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    norm_num
  apply hsum.of_norm_bounded_eventually_nat
  have ht := tendsto_realPowerDegree hq0
  have htr := (tendsto_natCast_atTop_atTop (R := ℝ)).comp ht
  filter_upwards [eventually_realPowerBlockLength_le_degree hq, ht.eventually_ge_atTop 4,
    htr.eventually_ge_atTop K] with j hj hN hKN
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact TailSupremum.appended_tail_supremum _ _ hN (realPowerBlockLength_pos hq.le j) hj hK hKN

/-- The maximal estimate controls every actual prefix difference in every
sufficiently late rounded real-power block. -/
theorem ae_eventually_real_power_prefix_difference {q : ℝ} (hq : 1 < q)
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, m ≤ realPowerBlockLength q j → ∀ z : ℂ,
        ‖z‖ ≤ 1 + K / realPowerDegree q j →
        ‖(rademacherPolynomial (realPowerDegree q j + m)
            (rademacherPrefix (realPowerDegree q j + m) ω)).eval z -
          (rademacherPolynomial (realPowerDegree q j)
            (rademacherPrefix (realPowerDegree q j) ω)).eval z‖ <
          TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) K := by
  let E (j : ℕ) : Set (SignVector (realPowerDegree q j + realPowerBlockLength q j)) := {v |
    ∃ m : ℕ, m ≤ realPowerBlockLength q j ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / realPowerDegree q j ∧
      TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) K ≤
        ‖(TailSupremum.appendedTailPolynomial
          (realPowerDegree q j) (realPowerBlockLength q j) m v).eval z‖}
  have h := ae_eventually_indexed_rademacherPrefix_notMem
    (fun j => realPowerDegree q j + realPowerBlockLength q j) E
    (summable_real_power_tail_failures hq K hK)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro m hm z hz
  have ht : ‖(TailSupremum.appendedTailPolynomial
      (realPowerDegree q j) (realPowerBlockLength q j) m
      (rademacherPrefix (realPowerDegree q j + realPowerBlockLength q j) ω)).eval z‖ <
      TailSupremum.tailAmplitude (realPowerDegree q j) (realPowerBlockLength q j) K :=
    lt_of_not_ge (fun hlarge => hj ⟨m, hm, z, hz, hlarge⟩)
  unfold rademacherPrefix at ht
  rw [TailSupremum.appendedTailPolynomial_eq_polynomialTail _ _ _ hm ω] at ht
  rw [rademacherPrefix_polynomial, rademacherPrefix_polynomial]
  rw [polynomialPrefix_eq_add_tail _ _ (Nat.le_add_right _ _),
    Polynomial.eval_add, add_sub_cancel_left]
  exact ht

end Erdos522
