/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BlockSupremaAlmostSure
import Erdos522.Limits.MovingRadialScales
import Erdos522.Stability.MovingRadiusMatching

/-!
# Almost-sure matching at moving radial targets

The common derivative and appended-tail events allow every polynomial in a
degree block to be compared with its initial prefix. For the radial target
`1 + x/n`, the reference thin band absorbs both root motion and target drift.
The same probability-one event applies to every fixed real `x`.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- On one probability-one event, each fixed radial coordinate admits eventual
matching throughout every degree block, with all unmatched multiplicities retained. -/
theorem ae_moving_radial_block_matching (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ x : ℝ, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let r := 1 + x / N
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
        Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
          (closedZeroCount P r) ≤
          closedZeroCount P (r + w) - closedZeroCount P (r - w) +
            zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ +
            annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ (1 / 64 : ℝ)) + m := by
  filter_upwards [ae_eventually_second_derivative_supremum K hK,
    ae_eventually_eighth_power_prefix_difference (K + 1) (by linarith)] with ω hD hT
  intro x
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  filter_upwards [ht.eventually hD, hT, eventually_eighth_power_root_localization K (K + 1),
    eventually_eighth_power_moving_radius_window (K + 1) x] with j hjD hjT hjS hjW
  dsimp only at hjS ⊢
  intro m hm
  let N := j ^ 8
  let P := rademacherPolynomial N (rademacherPrefix N ω)
  let Q := rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)
  let G := Q - P
  have hsum : P + G = Q := by simp [G]
  have hdeg : Q.natDegree - P.natDegree = m := by
    have hP : P.natDegree = N := rademacherPolynomial_prefix_natDegree ω N
    have hQ : Q.natDegree = N + m := rademacherPolynomial_prefix_natDegree ω (N + m)
    rw [hP, hQ]
    omega
  have hG (z : ℂ) (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
      ‖G.eval z‖ < TailSupremum.tailAmplitude N (eighthPowerBlockLength j) (K + 1) := by
    simpa only [G, Q, P, Polynomial.eval_sub] using hjT m hm z hz
  have hmatch := annular_root_matching_moving_radius P G (1 + x / N) (1 + x / (N + m : ℕ))
    hjS.1 hjS.2.1 hjS.2.2.1 hjS.2.2.2.1 (hjW m hm) hjD hG
  rw [hsum, hdeg] at hmatch
  exact hmatch

/-- The derivative-small root count contributes at most `N^(31/32)` to
moving-radius block matching, simultaneously for each fixed real coordinate. -/
theorem ae_moving_radial_block_count_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ x : ℝ, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let r := 1 + x / N
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
          (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (31 / 32 : ℝ) + m := by
  filter_upwards [ae_moving_radial_block_matching K hK,
    ae_eventually_annular_small_derivative_count K hK] with ω hM hB
  intro x
  filter_upwards [hM x, hB] with j hjM hjB
  dsimp only at hjM ⊢
  intro m hm
  have h := hjM m hm
  have hr : (Nat.dist (closedZeroCount
      (rademacherPolynomial (j ^ 8 + m) (rademacherPrefix (j ^ 8 + m) ω))
        (1 + x / (j ^ 8 + m : ℕ)))
      (closedZeroCount (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        (1 + x / (j ^ 8 : ℕ))) : ℝ) ≤
      (closedZeroCount (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        (1 + x / (j ^ 8 : ℕ) + radialMatchingWindow (j ^ 8)) -
       closedZeroCount (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        (1 + x / (j ^ 8 : ℕ) - radialMatchingWindow (j ^ 8)) : ℕ) +
      (zeroCountIn (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        {z | |‖z‖ - 1| ≤ K / (j ^ 8 : ℕ)}ᶜ : ℝ) +
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) K
          (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) + m := by exact_mod_cast h
  linarith

/-- A single probability-one event supplies the moving-radius block bound
at every integer annular width and every fixed real radial coordinate. -/
theorem ae_forall_moving_radial_block_count_bound :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ K : ℕ, ∀ x : ℝ, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let r := 1 + x / N
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j →
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) (1 + x / (N + m : ℕ)))
          (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ (K : ℝ) / N}ᶜ : ℝ) +
            (N : ℝ) ^ (31 / 32 : ℝ) + m := by
  apply ae_all_iff.mpr
  intro K
  exact ae_moving_radial_block_count_bound K (Nat.cast_nonneg K)

end Erdos522
