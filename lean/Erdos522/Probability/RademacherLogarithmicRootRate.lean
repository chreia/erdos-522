/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogarithmicRootRateEnvelope
import Erdos522.Probability.GrowingAnnularRootMatching
import Erdos522.Stability.NormalizedRootMatching

/-!
# The logarithmic almost-sure root-count rate

Shrinking Jensen probes control the matching window, while logarithmically
growing annuli contain all but `2 log 2 / K` of the root mass. Root matching
and exact block normalization retain the limiting constant `2000 log 2`.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The complete finite error envelope controls every degree in every sufficiently
late block on one almost-sure event. -/
theorem exists_ae_logarithmic_root_rate_envelope :
    ∃ H B : ℝ, 0 < H ∧ 0 < B ∧ ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, m ≤ realPowerBlockLength 8 j →
        |rademacherRadialFraction ω (realPowerDegree 8 j + m) 1 - 1 / 2| ≤
          logarithmicRootRateEnvelope H B j := by
  obtain ⟨H, hH, hthin⟩ := exists_ae_thin_radial_bound
  obtain ⟨B, hB, hmass⟩ := exists_ae_growing_annular_mass_bound (q := 8) (by norm_num)
  refine ⟨H, B, hH, hB, ?_⟩
  filter_upwards [hthin, hmass, ae_eventually_growing_annular_block_count_bound] with ω hωthin hωmass hωmatch
  filter_upwards [hωthin, hωmass, hωmatch,
    (tendsto_realPowerDegree (by norm_num : (0 : ℝ) < 8)).eventually_ge_atTop 1]
    with j hjthin hjmass hjmatch hN
  dsimp only at hjthin hjmass hjmatch
  intro m hm
  let N := realPowerDegree 8 j
  let P := rademacherPolynomial N (rademacherPrefix N ω)
  let Q := rademacherPolynomial (N + m) (rademacherPrefix (N + m) ω)
  let K := logarithmicAnnularWidth N
  let w := radialMatchingWindow N
  have hn : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hw : 0 ≤ w := by unfold w radialMatchingWindow; positivity
  have hcenter : |(closedZeroCount P 1 : ℝ) / N - 1 / 2| ≤ thinRadialError H N :=
    hjthin 1 (by simpa only [sub_self, abs_zero] using hw)
  have hinner : |(closedZeroCount P (1 - w) : ℝ) / N - 1 / 2| ≤ thinRadialError H N :=
    hjthin (1 - w) (by change |1 - w - 1| ≤ w; rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hw])
  have houter : |(closedZeroCount P (1 + w) : ℝ) / N - 1 / 2| ≤ thinRadialError H N :=
    hjthin (1 + w) (by change |1 + w - 1| ≤ w; rw [add_sub_cancel_left, abs_of_nonneg hw])
  have hbound := normalized_root_count_error_of_matching P Q hn hw hcenter hinner houter (hjmatch m hm 1)
  have hpower : (N : ℝ) ^ (31 / 32 : ℝ) / N = (N : ℝ) ^ (-(1 / 32 : ℝ)) := by
    rw [← Real.rpow_sub_one hNr.ne']
    congr 1
    norm_num
  have hmass' : (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤ growingAnnularMassEnvelope B N := hjmass
  have hm' : (m : ℝ) / N ≤ (realPowerBlockLength 8 j : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm) hNr.le
  change |(closedZeroCount Q 1 : ℝ) / ((N + m : ℕ) : ℝ) - 1 / 2| ≤ _
  rw [Nat.cast_add]
  unfold logarithmicRootRateEnvelope
  rw [hpower] at hbound
  norm_num at hbound
  dsimp only [N, P, K] at hmass'
  dsimp only [N] at *
  simp only [mul_div_assoc] at hbound ⊢
  linarith

/-- The almost-sure root fraction converges at the explicit logarithmic upper rate. -/
theorem ae_rademacher_logarithmic_root_rate :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      limsup (fun n : ℕ => Real.log n * |rademacherRadialFraction ω n 1 - 1 / 2|) atTop ≤
        2000 * Real.log 2 := by
  obtain ⟨H, B, _, hB, hbound⟩ := exists_ae_logarithmic_root_rate_envelope
  filter_upwards [hbound] with ω hω
  apply limsup_logarithmic_rate_of_block_bounds
    (strictMono_realPowerDegree (by norm_num : (1 : ℝ) ≤ 8))
    (tendsto_realPowerDegree_ratio (by norm_num : (1 : ℝ) < 8))
    (fun n => abs_nonneg (rademacherRadialFraction ω n 1 - 1 / 2))
    (tendsto_log_mul_logarithmicRootRateEnvelope H hB)
  filter_upwards [hω] with j hj
  intro n hnl hnu
  let m := n - realPowerDegree 8 j
  have hnm : realPowerDegree 8 j + m = n := Nat.add_sub_of_le hnl
  have hm : m ≤ realPowerBlockLength 8 j := by
    have hend := realPowerBlockLength_endpoint (by norm_num : (1 : ℝ) ≤ 8) j
    omega
  simpa only [hnm] using hj m hm

end Erdos522
