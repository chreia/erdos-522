/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GrowingAnnularSuprema
import Erdos522.Limits.GrowingAnnularLocalization
import Erdos522.Probability.RealPowerRootMatching

/-!
# Root matching throughout a logarithmically growing annulus

The growing-width derivative, tail, and mesh bounds hold on the same coin
sequence. Their deterministic localization margins yield an all-radii
comparison on every sufficiently late eighth-power degree block.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The growing annulus gives a simultaneous block matching inequality, with
at most `N^(31/32)` unmatched roots of small derivative. -/
theorem ae_eventually_growing_annular_block_count_bound :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree 8 j
      let K := logarithmicAnnularWidth N
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ realPowerBlockLength 8 j → ∀ r : ℝ,
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r) (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (31 / 32 : ℝ) + m := by
  have hK : ∀ᶠ N : ℕ in atTop, 0 ≤ logarithmicAnnularWidth N ∧ logarithmicAnnularWidth N + 1 ≤ N :=
    eventually_logarithmicAnnularWidth_add_one_le_degree.mono
      (fun N hN => ⟨logarithmicAnnularWidth_nonneg N, hN⟩)
  have hK' : ∀ᶠ N : ℕ in atTop, 0 ≤ logarithmicAnnularWidth N + 1 ∧ logarithmicAnnularWidth N + 1 ≤ N :=
    hK.mono (fun _ hN => ⟨by linarith [hN.1], hN.2⟩)
  filter_upwards [ae_eventually_second_derivative_supremum_of_width_sequence logarithmicAnnularWidth hK,
    ae_eventually_real_power_prefix_difference_of_width_sequence (by norm_num : (1 : ℝ) < 8)
      (fun N => logarithmicAnnularWidth N + 1) hK',
    ae_eventually_growing_annular_derivative_count (q := 8) (by norm_num)] with ω hD hT hB
  have ht := tendsto_realPowerDegree (by norm_num : (0 : ℝ) < 8)
  filter_upwards [ht.eventually hD, hT, hB, eventually_growing_annular_root_localization,
    ht.eventually_ge_atTop 1] with j hjD hjT hjB hjS hN
  dsimp only at hjT hjB hjS ⊢
  intro m hm r
  let N := realPowerDegree 8 j
  let K := logarithmicAnnularWidth N
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
      ‖G.eval z‖ < TailSupremum.tailAmplitude N (realPowerBlockLength 8 j) (K + 1) := by
    simpa only [G, Q, P, Polynomial.eval_sub] using hjT m hm z hz
  have hmatch := annular_root_matching P G r hjS.1 hjS.2.1 hjS.2.2.1 hjS.2.2.2.1
    hjS.2.2.2.2 hjD hG
  rw [hsum, hdeg] at hmatch
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hthreshold : (N : ℝ) ^ (3 / 2 - (1 / 64 : ℝ)) =
      (N : ℝ) ^ (3 / 2 : ℝ) / (N : ℝ) ^ (1 / 64 : ℝ) := Real.rpow_sub hn _ _
  change Nat.dist (closedZeroCount Q r) (closedZeroCount P r) ≤
    closedZeroCount P (r + radialMatchingWindow N) - closedZeroCount P (r - radialMatchingWindow N) +
      zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ +
      zeroCountIn P {z | |‖z‖ - 1| ≤ K / N ∧
        ‖P.derivative.eval z‖ ≤ (N : ℝ) ^ (3 / 2 - (1 / 64 : ℝ))} + m at hmatch
  rw [hthreshold] at hmatch
  change Nat.dist _ _ ≤ _ + _ + annularSmallDerivativeZeroCount _ _ _ _ + m at hmatch
  have hr : (Nat.dist (closedZeroCount Q r) (closedZeroCount P r) : ℝ) ≤
      (closedZeroCount P (r + radialMatchingWindow N) - closedZeroCount P (r - radialMatchingWindow N) : ℕ) +
      (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) +
      (annularSmallDerivativeZeroCount P N K ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ) + m := by
    exact_mod_cast hmatch
  change (Nat.dist (closedZeroCount Q r) (closedZeroCount P r) : ℝ) ≤
    (closedZeroCount P (r + radialMatchingWindow N) - closedZeroCount P (r - radialMatchingWindow N) : ℕ) +
      (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (31 / 32 : ℝ) + m
  linarith

end Erdos522
