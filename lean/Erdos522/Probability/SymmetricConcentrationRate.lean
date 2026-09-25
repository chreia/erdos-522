/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricLogarithmicConcentration
import Erdos522.Probability.LogarithmicConcentrationRate
import Erdos522.Probability.BoundedOccupation
import Erdos522.Probability.BoundedComplexHoeffding

/-!
# Logarithmic concentration rates with bounded coefficient energy

The extra positive-log tail from a coefficient bound is negligible at the
radial Jensen tolerance. Exponential energy failures are absorbed into the
same polynomial probability budget as the occupation errors.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology
namespace Erdos522

/-- Any fixed positive-log tail coefficient is absorbed by a vanishing
relative error at the standard logarithmic clipping scale. -/
theorem logarithmic_energy_threshold_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {A H c : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ c) :
    logarithmicTolerance N / 2 + 2 * (Real.log N / 32) * (H / Real.sqrt N) +
        logarithmicMomentCutoff A N * Real.sqrt
          (Real.exp (-2 * (Real.log N / 32)) + H / Real.sqrt N + (N : ℝ) ^ (-1 / 16 : ℝ)) +
        c * Real.exp (-2 * (Real.log N / 32)) ≤
      logarithmicTolerance N / 2 +
        (logarithmicRelativeError A H N + c * (N : ℝ) ^ (-1 / 32 : ℝ)) * logarithmicTolerance N := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have hp7 : 1 ≤ (Real.log N) ^ 7 := one_le_pow₀ hlog
  have hpow : (N : ℝ) ^ (-1 / 32 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ) =
      (N : ℝ) ^ (-1 / 16 : ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  have htail : c * Real.exp (-2 * (Real.log N / 32)) ≤
      (c * (N : ℝ) ^ (-1 / 32 : ℝ)) * logarithmicTolerance N := by
    rw [logarithmic_clipping_exp hn]
    calc
      _ ≤ c * (N : ℝ) ^ (-1 / 16 : ℝ) * (Real.log N) ^ 7 := by
        convert mul_le_mul_of_nonneg_left hp7
          (show 0 ≤ c * (N : ℝ) ^ (-1 / 16 : ℝ) by positivity) using 1
        ring
      _ = _ := by
        unfold logarithmicTolerance
        rw [show c * (N : ℝ) ^ (-1 / 32 : ℝ) *
            ((N : ℝ) ^ (-1 / 32 : ℝ) * Real.log N ^ 7) =
          c * ((N : ℝ) ^ (-1 / 32 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) * Real.log N ^ 7 by ring, hpow]
  have h := logarithmic_threshold_le (A := A) hlog hH
  nlinarith [Real.exp_pos (-2 * (Real.log N / 32))]

/-- Every fixed exponential energy failure is eventually bounded by the
logarithmic-concentration probability power. -/
theorem eventually_exponential_le_logarithmic_power (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-c * N) ≤ (N : ℝ) ^ (-3 / 8 : ℝ) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 8) c hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1,
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN hsmall
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := Real.rpow_pos_of_pos hn (3 / 8 : ℝ)
  have hh : Real.exp (-c * N) ≤ 1 / (N : ℝ) ^ (3 / 8 : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    simpa only [Function.comp_def, mul_comm] using hsmall.le
  simpa only [show (-3 / 8 : ℝ) = -(3 / 8 : ℝ) by ring, Real.rpow_neg hn.le, one_div] using hh

/-- Unconditioned occupation estimates and the actual event-restricted
logarithmic theorem imply a summable polynomial failure rate. -/
theorem eventually_symmetric_logarithmic_concentration_of_occupation
    (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (B K H : ℝ) (hB : 0 < B) (hK : 0 ≤ K) (hH : 0 < H)
    (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    (hocc : ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N → ∀ t : ℝ,
      |(∫ a, levelOccupation radianIntervalMeasure (normalizedCoefficientValueModulus N r) (t, a)
          ∂Measure.pi (fun _ : Fin (N + 1) => μ)) -
        circularGaussian.real (closedBall 0 (Real.exp t))| ≤ H / Real.sqrt N ∧
      variance (fun a => levelOccupation radianIntervalMeasure
        (normalizedCoefficientValueModulus N r) (t, a)) (Measure.pi (fun _ : Fin (N + 1) => μ)) ≤ H / Real.sqrt N) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real {a | logarithmicTolerance N <
        |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} ≤
          (2 * H + 2) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  let A := LogMoments.amplitudeLogarithmicConstant B
  let c := B ^ 2 / 2 + 1
  have hA : 0 < A := amplitude_logarithmic_constant_pos B
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he := (tendsto_logarithmicRelativeError A H).add
    (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul c)
  simp only [mul_zero, add_zero, Function.comp_def] at he
  have henergy := eventually_exponential_le_logarithmic_power
    (1 / (2 * B ^ 4 * Real.exp (6 * K))) (by positivity)
  filter_upwards [hocc, eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1,
    he.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2), henergy]
      with N hoccN hN hNK hlog herror henergyN
  change 1 ≤ Real.log N at hlog
  intro r hrl hru
  have hn : 1 < N := by omega
  have hn0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn0
  have htol := logarithmicTolerance_pos hn
  have hD : 0 < logarithmicMomentCutoff A N := by
    unfold logarithmicMomentCutoff
    have hl : 0 < Real.log N := by linarith
    positivity
  have hthreshold := (logarithmic_energy_threshold_le (A := A) hlog hH.le hc).trans
    (show logarithmicTolerance N / 2 +
      (logarithmicRelativeError A H N + c * (N : ℝ) ^ (-1 / 32 : ℝ)) * logarithmicTolerance N ≤
      logarithmicTolerance N by nlinarith)
  have hd : 0 ≤ H / Real.sqrt N := by positivity
  have h := symmetric_logarithmic_integral_concentration N hn0
    (fun _ : Fin (N + 1) => μ) K r B hK hNK hrl hru hB (fun _ => hbound) (fun _ => hsecond)
    (H / Real.sqrt N) (H / Real.sqrt N) hd hd
    (fun t => (hoccN r hrl hru t).1) (fun t => (hoccN r hrl hru t).2)
    (Real.log N) hlog (Real.log N / 32) (logarithmicTolerance N / 2)
    ((N : ℝ) ^ (-1 / 16 : ℝ)) (logarithmicMomentCutoff A N)
    (by linarith) (by positivity) (Real.rpow_pos_of_pos hNr _) hD
  have hprob := (measure_mono (μ := Measure.pi (fun _ : Fin (N + 1) => μ)) (show
      {a | logarithmicTolerance N <
        |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} ⊆
      {a | logarithmicTolerance N / 2 + 2 * (Real.log N / 32) * (H / Real.sqrt N) +
        logarithmicMomentCutoff A N * Real.sqrt
          (Real.exp (-2 * (Real.log N / 32)) + H / Real.sqrt N + (N : ℝ) ^ (-1 / 16 : ℝ)) +
        c * Real.exp (-2 * (Real.log N / 32)) <
        |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|}
      from fun _ ha => lt_of_le_of_lt hthreshold ha)).trans h
  have hscale := logarithmic_failure_le hlog hA hH.le
  have henergy' : Real.exp (-(N : ℝ) / (2 * B ^ 4 * Real.exp (6 * K))) ≤
      (N : ℝ) ^ (-3 / 8 : ℝ) := by
    convert henergyN using 1
    congr 1
    ring
  have hfinal := hprob.trans (ENNReal.ofReal_le_ofReal (show
      Real.exp (-(N : ℝ) / (2 * B ^ 4 * Real.exp (6 * K))) +
        (H / Real.sqrt N) / ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 +
        (A * (2 * Real.log N)) ^ (12 * Real.log N) / (logarithmicMomentCutoff A N ^ 2) ^ Real.log N +
        4 * (Real.log N / 32) ^ 2 * (H / Real.sqrt N) / (logarithmicTolerance N / 2) ^ 2 ≤
        (2 * H + 2) * (N : ℝ) ^ (-3 / 8 : ℝ) by linarith))
  have hnneg : 0 ≤ (2 * H + 2) * (N : ℝ) ^ (-3 / 8 : ℝ) := by positivity
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal

/-- A finite coefficient dominating both bounded-law occupation errors. -/
def boundedOccupationConstant (C B K : ℝ) : ℝ :=
  1 + |boundedValueGaussianErrorConstant C B K + 1 / Real.pi| +
    |boundedValuePairGaussianErrorConstant C B K + 2 * boundedValueGaussianErrorConstant C B K + 6 / Real.pi|

theorem boundedOccupationConstant_pos (C B K : ℝ) : 0 < boundedOccupationConstant C B K := by
  unfold boundedOccupationConstant
  positivity

/-- Bounded centrally symmetric unit-variance coefficient laws have the
actual uniform annular logarithmic concentration rate. -/
theorem exists_eventually_symmetric_logarithmic_concentration :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
      (B : ℝ) (_ : 0 < B) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
      (K : ℝ) (_ : 0 ≤ K), ∀ᶠ N : ℕ in atTop,
      ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
        (Measure.pi (fun _ : Fin (N + 1) => μ)).real {a | logarithmicTolerance N <
          |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} ≤
            (2 * boundedOccupationConstant C B K + 2) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  obtain ⟨C, hC, hocc⟩ := exists_bounded_coefficient_occupation_constant
  refine ⟨C, hC, ?_⟩
  intro μ _ _ B hB hbound hsecond K hK
  apply eventually_symmetric_logarithmic_concentration_of_occupation μ B K
    (boundedOccupationConstant C B K) hB hK (boundedOccupationConstant_pos C B K) hbound hsecond
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2)]
      with N hN hNK hdegree
  intro r hrl hru t
  have hb := hocc μ B hB.le hbound (integral_id_eq_zero_of_negInvariant μ) hsecond
    N (by omega) K r hK hNK hrl hru hdegree t
  constructor
  · refine hb.1.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    unfold boundedOccupationConstant
    linarith [le_abs_self (boundedValueGaussianErrorConstant C B K + 1 / Real.pi),
      abs_nonneg (boundedValuePairGaussianErrorConstant C B K + 2 * boundedValueGaussianErrorConstant C B K + 6 / Real.pi)]
  · refine hb.2.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    unfold boundedOccupationConstant
    linarith [le_abs_self (boundedValuePairGaussianErrorConstant C B K + 2 * boundedValueGaussianErrorConstant C B K + 6 / Real.pi),
      abs_nonneg (boundedValueGaussianErrorConstant C B K + 1 / Real.pi)]

end Erdos522
