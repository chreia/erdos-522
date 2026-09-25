/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RealPowerConcentration
import Erdos522.Probability.BlockSupremaAlmostSure
import Erdos522.Limits.RealPowerLocalization
import Erdos522.Stability.AnnularRootMatching

/-!
# Root matching on rounded real-power degree blocks

The derivative and maximal-tail estimates hold on one infinite coin space.
Their localization margins give a comparison simultaneously for every
partial block and every target radius. The two unmatched-root terms retain
their multiplicities.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The real-power block comparison at any admissible derivative and radial scales. -/
theorem ae_eventually_real_power_root_matching {q ℓ κ : ℝ} (hq : 1 < q)
    (hκ : 0 ≤ κ) (hisolation : 2 * ℓ < 1 / (2 * q))
    (hwindow : ℓ + κ < 1 / (2 * q)) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let w := (N : ℝ) ^ (-1 - κ)
      ∀ m : ℕ, m ≤ realPowerBlockLength q j → ∀ r : ℝ,
        Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r) (closedZeroCount P r) ≤
          closedZeroCount P (r + w) - closedZeroCount P (r - w) +
            zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ +
            zeroCountIn P {z | |‖z‖ - 1| ≤ K / N ∧
              ‖P.derivative.eval z‖ ≤ (N : ℝ) ^ (3 / 2 - ℓ)} + m := by
  filter_upwards [ae_eventually_second_derivative_supremum K hK,
    ae_eventually_real_power_prefix_difference hq (K + 1) (by linarith)] with ω hD hT
  have ht := tendsto_realPowerDegree (show 0 < q by linarith)
  filter_upwards [ht.eventually hD, hT,
    eventually_real_power_root_localization hq hκ hisolation hwindow K (K + 1)]
      with j hjD hjT hjS
  dsimp only at hjS ⊢
  intro m hm r
  let N := realPowerDegree q j
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
      ‖G.eval z‖ < TailSupremum.tailAmplitude N (realPowerBlockLength q j) (K + 1) := by
    simpa only [G, Q, P, Polynomial.eval_sub] using hjT m hm z hz
  have hmatch := annular_root_matching P G r hjS.1 hjS.2.1 hjS.2.2.1 hjS.2.2.2.1
    hjS.2.2.2.2 hjD hG
  rw [hsum, hdeg] at hmatch
  exact hmatch

/-- With the fixed scales `ℓ = κ = 1/64`, every `8/3 < q < 16` gives an
almost-sure block comparison with at most `N^(31/32)` derivative-small roots. -/
theorem ae_eventually_real_power_block_count_bound {q : ℝ}
    (hq : 8 / 3 < q) (hq16 : q < 16) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      let P := rademacherPolynomial N (rademacherPrefix N ω)
      let w := radialMatchingWindow N
      ∀ m : ℕ, m ≤ realPowerBlockLength q j → ∀ r : ℝ,
        (Nat.dist (closedZeroCount
          (rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)) r) (closedZeroCount P r) : ℝ) ≤
          (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) +
            (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) + (N : ℝ) ^ (31 / 32 : ℝ) + m := by
  have hq1 : 1 < q := by linarith
  have hmargin : (1 / 32 : ℝ) < 1 / (2 * q) := by
    apply (lt_div_iff₀ (by linarith : 0 < 2 * q)).mpr
    linarith
  have hisolation : 2 * (1 / 64 : ℝ) < 1 / (2 * q) := by linarith
  have hwindow : (1 / 64 : ℝ) + 1 / 64 < 1 / (2 * q) := by linarith
  filter_upwards [ae_eventually_real_power_root_matching hq1 (by norm_num : (0 : ℝ) ≤ 1 / 64)
      hisolation hwindow K hK,
    ae_eventually_real_power_annular_small_derivative_count hq K hK] with ω hM hB
  filter_upwards [hM, hB,
    (tendsto_realPowerDegree (show 0 < q by linarith)).eventually_ge_atTop 1] with j hjM hjB hN
  dsimp only at hjM ⊢
  intro m hm r
  have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast (show 0 < realPowerDegree q j by omega)
  have hthreshold : (realPowerDegree q j : ℝ) ^ (3 / 2 - (1 / 64 : ℝ)) =
      (realPowerDegree q j : ℝ) ^ (3 / 2 : ℝ) /
        (realPowerDegree q j : ℝ) ^ (1 / 64 : ℝ) := Real.rpow_sub hn _ _
  have h := hjM m hm r
  rw [hthreshold] at h
  change Nat.dist _ _ ≤ _ + _ + annularSmallDerivativeZeroCount _ _ _ _ + m at h
  have hr : (Nat.dist (closedZeroCount
      (rademacherPolynomial (realPowerDegree q j + m)
        (rademacherPrefix (realPowerDegree q j + m) ω)) r)
      (closedZeroCount (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω)) r) : ℝ) ≤
      (closedZeroCount (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω))
          (r + radialMatchingWindow (realPowerDegree q j)) -
       closedZeroCount (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω))
          (r - radialMatchingWindow (realPowerDegree q j)) : ℕ) +
      (zeroCountIn (rademacherPolynomial (realPowerDegree q j)
        (rademacherPrefix (realPowerDegree q j) ω))
          {z | |‖z‖ - 1| ≤ K / realPowerDegree q j}ᶜ : ℝ) +
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
          (realPowerDegree q j) K ((realPowerDegree q j : ℝ) ^ (1 / 64 : ℝ)) : ℝ) + m := by
    unfold radialMatchingWindow
    exact_mod_cast h
  linarith

end Erdos522
