/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GrowingLogarithmicTolerance

/-!
# Logarithmic concentration on a growing annulus

The radius-uniform finite concentration theorem applies at logarithmic
annular width once its explicit degree thresholds hold. Its finite clipping
threshold lies below the growing-width tolerance, and direct substitution
gives a summable failure envelope on the eighth-power schedule.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The growing-width logarithmic failure budget, expressed with a fixed coefficient. -/
def growingLogarithmicFailureEnvelope (H : ℝ) (N : ℕ) : ℝ :=
  H * (N : ℝ) ^ (-39 / 128 : ℝ) + (N : ℝ) ^ (-12 : ℝ) +
    H / 256 * (N : ℝ) ^ (-47 / 128 : ℝ) * (Real.log N) ^ 2

theorem logarithmicAnnularWidth_logarithmic_failure_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {B : ℝ} (hB : 0 < B) :
    logarithmicPowerFailure (1 / 32) (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N ≤
      growingLogarithmicFailureEnvelope (rademacherOccupationConstant B 0) N := by
  have hn : (0 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith) |>.trans' one_pos
  have hH := logarithmicAnnularWidth_occupationConstant_le hlog hB
  unfold logarithmicPowerFailure growingLogarithmicFailureEnvelope
  have hp (a : ℝ) : ((N : ℝ) ^ (9 / 128 : ℝ) * (N : ℝ) ^ a) =
      (N : ℝ) ^ (9 / 128 + a) := (Real.rpow_add hn _ _).symm
  calc
    _ ≤ (rademacherOccupationConstant B 0 * (N : ℝ) ^ (9 / 128 : ℝ)) *
        (N : ℝ) ^ (-1 / 2 + 4 * (1 / 32 : ℝ)) + (N : ℝ) ^ (-12 : ℝ) +
      4 * (1 / 32 : ℝ) ^ 2 * (rademacherOccupationConstant B 0 * (N : ℝ) ^ (9 / 128 : ℝ)) *
        (N : ℝ) ^ (-1 / 2 + 2 * (1 / 32 : ℝ)) * (Real.log N) ^ 2 := by gcongr
    _ = rademacherOccupationConstant B 0 *
        ((N : ℝ) ^ (9 / 128 : ℝ) * (N : ℝ) ^ (-1 / 2 + 4 * (1 / 32 : ℝ))) +
        (N : ℝ) ^ (-12 : ℝ) + (rademacherOccupationConstant B 0 / 256) *
          ((N : ℝ) ^ (9 / 128 : ℝ) * (N : ℝ) ^ (-1 / 2 + 2 * (1 / 32 : ℝ))) *
            (Real.log N) ^ 2 := by ring
    _ = _ := by rw [hp, hp]; norm_num

/-- The exact radius and covariance thresholds hold eventually at logarithmic width. -/
theorem eventually_logarithmicAnnularWidth_degree_conditions :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 1 ≤ Real.log N ∧
      2 * logarithmicAnnularWidth N ≤ N ∧
      (6400 * Real.exp (8 * logarithmicAnnularWidth N)) ^ 2 ≤ (N : ℝ) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  have hwidth := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul (2 / 128 : ℝ)
  simp only [pow_one, Real.rpow_one, mul_zero] at hwidth
  have hcov := (tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 7 / 8)).const_mul (6400 ^ 2 : ℝ)
  simp only [mul_zero, ← neg_div] at hcov
  filter_upwards [eventually_ge_atTop 2, hlog,
    hwidth.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    hcov.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with N hN hl hw hc
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN, hl, ?_, ?_⟩
  · have hW := logarithmicAnnularWidth_le hl
    have hw' : (2 * Real.log N / 128) / N < 1 := by convert hw using 1; ring
    have := (div_lt_one hn).mp hw'
    linarith
  · exact (div_le_one₀ hn).mp ((logarithmicAnnularWidth_covariance_ratio_le hl).trans hc.le)

/-- The actual sign-law logarithmic estimate is uniform over the logarithmically
growing annulus and has a fixed summable failure envelope. -/
theorem exists_growing_annular_logarithmic_concentration :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      ∀ r : ℝ, 1 - logarithmicAnnularWidth N / N ≤ r →
        r ≤ 1 + logarithmicAnnularWidth N / N →
        (signMeasure N).real {ω |
          growingLogarithmicTolerance (fourierLogarithmicConstant harmonicRestrictionConstant)
            (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N <
          |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|} ≤
            growingLogarithmicFailureEnvelope (rademacherOccupationConstant B 0) N := by
  obtain ⟨B, hB, hbound⟩ := exists_rademacher_logarithmic_concentration_constant
    one_le_harmonicRestrictionConstant harmonic_l2_restriction
  refine ⟨B, hB, ?_⟩
  let A := fourierLogarithmicConstant harmonicRestrictionConstant
  have hA : 0 < A := fourierLogarithmicConstant_pos one_le_harmonicRestrictionConstant
  filter_upwards [eventually_logarithmicAnnularWidth_degree_conditions] with N hN
  intro r hrl hru
  let K := logarithmicAnnularWidth N
  let H := rademacherOccupationConstant B K
  have hH : 0 < H := rademacherOccupationConstant_pos B K
  have hn : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hlog : 0 < Real.log N := by linarith [hN.2.1]
  have hD : 0 < powerLogarithmicMomentCutoff A N := by unfold powerLogarithmicMomentCutoff; positivity
  have hthreshold := growing_logarithmic_threshold_le (by omega : 1 ≤ N) A hH.le
  have h := hbound N hn K r (logarithmicAnnularWidth_nonneg N) hN.2.2.1 hrl hru hN.2.2.2
    (6 * Real.log N) (by linarith [hN.2.1]) ((1 / 32 : ℝ) * Real.log N)
    ((N : ℝ) ^ (-(1 / 32 : ℝ))) ((N : ℝ) ^ (-2 * (1 / 32 : ℝ)))
    (powerLogarithmicMomentCutoff A N) (by positivity)
    (Real.rpow_pos_of_pos hNr _) (Real.rpow_pos_of_pos hNr _) hD
  have hprob := (measure_mono (μ := signMeasure N) (show
      {ω | growingLogarithmicTolerance A H N <
        |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|} ⊆
      {ω | (N : ℝ) ^ (-(1 / 32 : ℝ)) + 2 * ((1 / 32 : ℝ) * Real.log N) * (H / Real.sqrt N) +
        powerLogarithmicMomentCutoff A N * Real.sqrt
          (Real.exp (-2 * ((1 / 32 : ℝ) * Real.log N)) + H / Real.sqrt N +
            (N : ℝ) ^ (-2 * (1 / 32 : ℝ))) +
        (3 / 2 : ℝ) * Real.exp (-2 * ((1 / 32 : ℝ) * Real.log N)) <
          |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|}
      from fun _ hω => lt_of_le_of_lt hthreshold hω)).trans h
  rw [logarithmic_power_failure_identity (by omega : 1 < N) hA] at hprob
  have hfinal := hprob.trans (ENNReal.ofReal_le_ofReal
    (logarithmicAnnularWidth_logarithmic_failure_le hN.2.1 hB))
  have hnonneg : 0 ≤ growingLogarithmicFailureEnvelope (rademacherOccupationConstant B 0) N := by
    have := rademacherOccupationConstant_pos B 0
    unfold growingLogarithmicFailureEnvelope
    positivity
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal

/-- The growing-annulus logarithmic exceptional probabilities are summable
on every rounded real-power schedule with exponent greater than `128/39`. -/
theorem summable_growingLogarithmicFailureEnvelope {q : ℝ} (hq : 128 / 39 < q) (H : ℝ) :
    Summable (fun j : ℕ => growingLogarithmicFailureEnvelope H (realPowerDegree q j)) := by
  have hq0 : 0 < q := by linarith
  have h₁ := (summable_realPowerDegree_rpow hq0
    (show q * (-39 / 128 : ℝ) < -1 by linarith)).mul_left H
  have h₂ := summable_realPowerDegree_rpow hq0 (show q * (-12 : ℝ) < -1 by linarith)
  have h₃ := (summable_realPowerDegree_rpow_mul_log_pow hq0
    (show q * (-47 / 128 : ℝ) < -1 by linarith) 2).mul_left (H / 256)
  apply (h₁.add h₂ |>.add h₃).congr
  intro j
  unfold growingLogarithmicFailureEnvelope
  ring

/-- The four Jensen probes at the scaled radii `-K`, `-(K - 1)`, `K - 1`, `K`. -/
def radialUnitGapRadii (K : ℝ) (N : ℕ) (i : Fin 4) : ℝ :=
  1 + ![-K, -(K - 1), K - 1, K] i / N

theorem radialUnitGapRadii_mem_annulus {K : ℝ} (hK : 1 ≤ K) (N : ℕ) (i : Fin 4) :
    1 - K / N ≤ radialUnitGapRadii K N i ∧ radialUnitGapRadii K N i ≤ 1 + K / N := by
  have hd : 0 ≤ K / N := div_nonneg (by linarith) (Nat.cast_nonneg N)
  have hd' : (K - 1) / (N : ℝ) ≤ K / N := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
  have hd'' : 0 ≤ (K - 1) / (N : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg N)
  have hneg : (1 - K) / (N : ℝ) = -((K - 1) / N) := by ring
  fin_cases i <;> simp [radialUnitGapRadii, neg_div] <;> (try constructor) <;> linarith

/-- Four Jensen probes in the growing annulus obey one simultaneous logarithmic
bound almost surely on every sufficiently sparse real-power schedule. -/
theorem exists_ae_growing_annular_logarithmic_bound {q : ℝ} (hq : 128 / 39 < q) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      let N := realPowerDegree q j
      let K := logarithmicAnnularWidth N
      |logCircleAverage (rademacherPolynomial N (rademacherPrefix N ω)) (radialUnitGapRadii K N i) -
        Real.log (radialSigma N (radialUnitGapRadii K N i)) - circularLogMean| ≤
          growingLogarithmicTolerance (fourierLogarithmicConstant harmonicRestrictionConstant)
            (rademacherOccupationConstant B K) N := by
  obtain ⟨B, hB, hbound⟩ := exists_growing_annular_logarithmic_concentration
  let A := fourierLogarithmicConstant harmonicRestrictionConstant
  let E (N : ℕ) : Set (SignVector N) := {v | ∃ i : Fin 4,
    growingLogarithmicTolerance A (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N <
      |logCircleAverage (rademacherPolynomial N v) (radialUnitGapRadii (logarithmicAnnularWidth N) N i) -
        Real.log (radialSigma N (radialUnitGapRadii (logarithmicAnnularWidth N) N i)) - circularLogMean|}
  have hprob : ∀ᶠ N : ℕ in atTop, (signMeasure N).real (E N) ≤
      4 * growingLogarithmicFailureEnvelope (rademacherOccupationConstant B 0) N := by
    filter_upwards [hbound, tendsto_logarithmicAnnularWidth_atTop.eventually_ge_atTop 1] with N hN hK
    have heq : E N = ⋃ i : Fin 4, {v |
      growingLogarithmicTolerance A (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N <
        |logCircleAverage (rademacherPolynomial N v) (radialUnitGapRadii (logarithmicAnnularWidth N) N i) -
          Real.log (radialSigma N (radialUnitGapRadii (logarithmicAnnularWidth N) N i)) - circularLogMean|} := by
      ext v
      simp [E]
    rw [heq]
    calc
      _ ≤ ∑ i : Fin 4, (signMeasure N).real {v |
          growingLogarithmicTolerance A (rademacherOccupationConstant B (logarithmicAnnularWidth N)) N <
            |logCircleAverage (rademacherPolynomial N v) (radialUnitGapRadii (logarithmicAnnularWidth N) N i) -
              Real.log (radialSigma N (radialUnitGapRadii (logarithmicAnnularWidth N) N i)) - circularLogMean|} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin 4, growingLogarithmicFailureEnvelope (rademacherOccupationConstant B 0) N := by
        apply Finset.sum_le_sum
        intro i _
        have hi := radialUnitGapRadii_mem_annulus hK N i
        exact hN _ hi.1 hi.2
      _ = _ := by simp
  have hs : Summable (fun j : ℕ => (signMeasure (realPowerDegree q j)).real (E (realPowerDegree q j))) := by
    apply ((summable_growingLogarithmicFailureEnvelope hq (rademacherOccupationConstant B 0)).mul_left 4).of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_realPowerDegree (show 0 < q by linarith)).eventually hprob] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hj
  refine ⟨B, hB, ?_⟩
  filter_upwards [ae_eventually_rademacherPrefix_notMem (realPowerDegree q) E hs] with ω hω
  filter_upwards [hω] with j hj
  intro i
  exact le_of_not_gt (fun hlarge => hj ⟨i, hlarge⟩)

end Erdos522
