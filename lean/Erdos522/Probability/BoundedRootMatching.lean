/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BoundedBlockSuprema
import Erdos522.Probability.BoundedAnnularSmallDerivativeRate
import Erdos522.Limits.BoundedRootLocalization
import Erdos522.Stability.MovingRadiusMatching

/-!
# Root matching for bounded symmetric coefficients at moving radial targets

The common derivative and appended-tail events allow every polynomial in a
degree block to be compared with its initial prefix. For the radial target
`1 + x/n`, the reference thin band absorbs both root motion and target drift.
The same probability-one event applies to every fixed real `x`, and a
logarithmic trailing-zero correction retains the actual degrees.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant] {B : ℝ}
    (hB : 1 ≤ B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)

include hB hbound hsecond

/-- On one probability-one event, each fixed radial coordinate admits eventual
matching throughout every degree block, with all unmatched multiplicities retained. -/
theorem ae_bounded_moving_radial_block_matching (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ x : ℝ, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := Polynomial.ofFn (N + 1) (coefficientPrefix N ω)
      let r := 1 + x / N
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
        Nat.dist (closedZeroCount
          (Polynomial.ofFn (N + m + 1) (coefficientPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
          (closedZeroCount P r) ≤
          closedZeroCount P (r + w) - closedZeroCount P (r - w) +
            zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ +
            annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ (1 / 64 : ℝ)) + m +
              ⌈zeroRunLogarithmicConstant μ * Real.log (N + 1 : ℕ)⌉₊ := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hmean := integral_id_eq_zero_of_negInvariant μ
  have hatom := zero_atom_lt_one_of_second_moment_one μ hsecond
  filter_upwards [ae_eventually_bounded_second_derivative_supremum μ hB0 hbound hmean K hK,
    ae_eventually_eighth_power_bounded_prefix_difference μ hB0 hbound hmean (K + 1) (by linarith),
    ae_eventually_actual_degree_correction μ hatom] with ω hD hT hdegree
  intro x
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  filter_upwards [ht.eventually hD, hT, ht.eventually hdegree,
    eventually_eighth_power_bounded_root_localization hB0 K (K + 1),
    eventually_eighth_power_bounded_moving_radius_window hB0 (K + 1) x]
      with j hjD hjT hjdegree hjS hjW
  dsimp only at hjS ⊢
  intro m hm
  let N := j ^ 8
  let P := Polynomial.ofFn (N + 1) (coefficientPrefix N ω)
  let Q := Polynomial.ofFn (N + m + 1) (coefficientPrefix (N + m) ω)
  let G := Q - P
  have hsum : P + G = Q := by simp [G]
  have hdeg : Q.natDegree - P.natDegree ≤ m +
      ⌈zeroRunLogarithmicConstant μ * Real.log (N + 1 : ℕ)⌉₊ := by
    simpa only [P, Q, coefficientPrefix_polynomial] using hjdegree.2 m
  have hG (z : ℂ) (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
      ‖G.eval z‖ < B * TailSupremum.tailAmplitude N (eighthPowerBlockLength j) (K + 1) := by
    simpa only [G, Q, P, Polynomial.eval_sub] using hjT m hm z hz
  have hmatch := annular_root_matching_moving_radius P G (1 + x / N) (1 + x / (N + m : ℕ))
    hjS.1 hjS.2.1 hjS.2.2.1 hjS.2.2.2.1 (hjW m hm) hjD hG
  rw [hsum] at hmatch
  dsimp only [P, Q, N, regularDerivativeThreshold, annularSmallDerivativeZeroCount] at hmatch hdeg ⊢
  omega

/-- The derivative-small root count contributes at most `N^(31/32)` to
moving-radius block matching, simultaneously for each fixed real coordinate. -/
theorem ae_bounded_moving_radial_block_count_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ x : ℝ, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := Polynomial.ofFn (N + 1) (coefficientPrefix N ω)
      let r := 1 + x / N
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
        (Nat.dist (closedZeroCount
          (Polynomial.ofFn (N + m + 1) (coefficientPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
          (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (31 / 32 : ℝ) + m +
              (⌈zeroRunLogarithmicConstant μ * Real.log (N + 1 : ℕ)⌉₊ : ℝ) := by
  filter_upwards [ae_bounded_moving_radial_block_matching μ hB hbound hsecond K hK,
    ae_eventually_bounded_annular_small_derivative_count μ hB hbound
      (integral_id_eq_zero_of_negInvariant μ) hsecond K hK] with ω hM hB
  intro x
  filter_upwards [hM x, hB] with j hjM hjB
  dsimp only at hjM ⊢
  intro m hm
  have h := hjM m hm
  have hr : (Nat.dist (closedZeroCount
      (Polynomial.ofFn (j ^ 8 + m + 1) (coefficientPrefix (j ^ 8 + m) ω))
        (1 + x / (j ^ 8 + m : ℕ)))
      (closedZeroCount (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω))
        (1 + x / (j ^ 8 : ℕ))) : ℝ) ≤
      (closedZeroCount (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω))
        (1 + x / (j ^ 8 : ℕ) + radialMatchingWindow (j ^ 8)) -
       closedZeroCount (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω))
        (1 + x / (j ^ 8 : ℕ) - radialMatchingWindow (j ^ 8)) : ℕ) +
      (zeroCountIn (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω))
        {z | |‖z‖ - 1| ≤ K / (j ^ 8 : ℕ)}ᶜ : ℝ) +
      (annularSmallDerivativeZeroCount
        (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω)) (j ^ 8) K
          (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) + m +
        (⌈zeroRunLogarithmicConstant μ * Real.log (j ^ 8 + 1 : ℕ)⌉₊ : ℝ) := by exact_mod_cast h
  linarith

/-- A single probability-one event supplies the moving-radius block bound
at every integer annular width and every fixed real radial coordinate. -/
theorem ae_forall_bounded_moving_radial_block_count_bound :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ K : ℕ, ∀ x : ℝ, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := Polynomial.ofFn (N + 1) (coefficientPrefix N ω)
      let r := 1 + x / N
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
        (Nat.dist (closedZeroCount
          (Polynomial.ofFn (N + m + 1) (coefficientPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
          (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ (K : ℝ) / N}ᶜ : ℝ) +
            (N : ℝ) ^ (31 / 32 : ℝ) + m +
              (⌈zeroRunLogarithmicConstant μ * Real.log (N + 1 : ℕ)⌉₊ : ℝ) := by
  apply ae_all_iff.mpr
  intro K
  exact ae_bounded_moving_radial_block_count_bound μ hB hbound hsecond K (Nat.cast_nonneg K)

end Erdos522
