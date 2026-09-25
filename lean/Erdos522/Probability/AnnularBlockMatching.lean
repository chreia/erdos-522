/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BlockSupremaAlmostSure
import Erdos522.Limits.RootLocalizationScales
import Erdos522.Stability.AnnularRootMatching

/-!
# Almost-sure matching throughout degree blocks

The derivative and appended-tail envelopes hold on the same infinite coin
space. Their localization scales allow the regular annular roots to be
matched simultaneously for every degree in a block and every target radius.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Almost surely, every sufficiently late degree block admits a root-count comparison
    at every radius. The unmatched terms retain their multiplicities. -/
theorem ae_eventually_annular_block_matching (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ r : ℝ,
        Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r) (closedZeroCount P r) ≤
          closedZeroCount P (r + w) - closedZeroCount P (r - w) +
            zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ +
            annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ (1 / 64 : ℝ)) + m := by
  filter_upwards [ae_eventually_second_derivative_supremum K hK,
    ae_eventually_eighth_power_prefix_difference (K + 1) (by linarith)] with ω hD hT
  have ht := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  filter_upwards [ht.eventually hD, hT, eventually_eighth_power_root_localization K (K + 1)]
    with j hjD hjT hjS
  dsimp only at hjS ⊢
  intro m hm r
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
  have hmatch := annular_root_matching P G r hjS.1 hjS.2.1 hjS.2.2.1 hjS.2.2.2.1
    hjS.2.2.2.2 hjD hG
  rw [hsum, hdeg] at hmatch
  exact hmatch

/-- The derivative-small term has its quantitative almost-sure bound, uniformly over
    all partial tails and radii within a sufficiently late block. -/
theorem ae_eventually_annular_block_count_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ r : ℝ,
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r) (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (31 / 32 : ℝ) + m := by
  filter_upwards [ae_eventually_annular_block_matching K hK,
    ae_eventually_annular_small_derivative_count K hK] with ω hM hB
  filter_upwards [hM, hB] with j hjM hjB
  dsimp only at hjM ⊢
  intro m hm r
  have h := hjM m hm r
  have hr : (Nat.dist (closedZeroCount
      (rademacherPolynomial (j ^ 8 + m) (rademacherPrefix (j ^ 8 + m) ω)) r)
      (closedZeroCount (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) r) : ℝ) ≤
      (closedZeroCount (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        (r + radialMatchingWindow (j ^ 8)) -
       closedZeroCount (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        (r - radialMatchingWindow (j ^ 8)) : ℕ) +
      (zeroCountIn (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        {z | |‖z‖ - 1| ≤ K / (j ^ 8 : ℕ)}ᶜ : ℝ) +
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) K
          (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) + m := by exact_mod_cast h
  linarith

/-- One event of probability one supplies the block comparison at all integer annular widths. -/
theorem ae_forall_annular_block_count_bound :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ K : ℕ, ∀ᶠ j : ℕ in atTop,
      let N := j ^ 8
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ eighthPowerBlockLength j → ∀ r : ℝ,
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r) (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ (K : ℝ) / N}ᶜ : ℝ) + (N : ℝ) ^ (31 / 32 : ℝ) + m := by
  apply ae_all_iff.mpr
  intro K
  exact ae_eventually_annular_block_count_bound K (Nat.cast_nonneg K)

end Erdos522
