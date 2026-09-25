/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausLogarithmicConcentration
import Erdos522.Probability.LogarithmicConcentrationRate

/-!
# Polynomial concentration rate for Steinhaus logarithmic averages

Choosing logarithmic moment order and the same clipping scales as in the
radial secant argument gives error `N^(-1/32) (log N)^7` with failure of
order `N^(-3/8)`, uniformly over each fixed-width annulus.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Erdos522

/-- Uniformity in the radius is retained while all scalar thresholds are absorbed
into a finite initial degree. -/
theorem exists_eventually_steinhaus_logarithmic_concentration :
    ∃ B : ℝ, 0 < B ∧ ∀ K : ℝ, 0 ≤ K → ∀ᶠ N : ℕ in atTop,
      ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
        (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω | logarithmicTolerance N <
          |logCircleAverage (Polynomial.ofFn (N + 1) ω) r - Real.log (radialSigma N r) - circularLogMean|} ≤
          (2 * steinhausOccupationConstant B K + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := exists_steinhaus_logarithmic_concentration_constant
  refine ⟨B, hB, ?_⟩
  intro K hK
  let H := steinhausOccupationConstant B K
  let A := LogMoments.amplitudeLogarithmicConstant 1
  have hH : 0 < H := steinhausOccupationConstant_pos B K
  have hA : 0 < A := steinhausLogarithmicConstant_pos
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1,
    (tendsto_logarithmicRelativeError A H).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
      with N hN hNK hdegree hlog herror
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
  have hthreshold := (logarithmic_threshold_le (A := A) hlog hH.le).trans
    (show logarithmicTolerance N / 2 + logarithmicRelativeError A H N * logarithmicTolerance N ≤
      logarithmicTolerance N by nlinarith)
  have h := hbound N hn0 K r hK hNK hrl hru hdegree (Real.log N) hlog
    (Real.log N / 32) (logarithmicTolerance N / 2) ((N : ℝ) ^ (-1 / 16 : ℝ))
    (logarithmicMomentCutoff A N) (by linarith) (by positivity)
    (Real.rpow_pos_of_pos hNr _) hD
  have hprob := (measure_mono (μ := Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)) (show
      {ω | logarithmicTolerance N <
        |logCircleAverage (Polynomial.ofFn (N + 1) ω) r - Real.log (radialSigma N r) - circularLogMean|} ⊆
      {ω | logarithmicTolerance N / 2 + 2 * (Real.log N / 32) * (H / Real.sqrt N) +
          logarithmicMomentCutoff A N * Real.sqrt
            (Real.exp (-2 * (Real.log N / 32)) + H / Real.sqrt N + (N : ℝ) ^ (-1 / 16 : ℝ)) +
          (3 / 2 : ℝ) * Real.exp (-2 * (Real.log N / 32)) <
        |logCircleAverage (Polynomial.ofFn (N + 1) ω) r - Real.log (radialSigma N r) - circularLogMean|}
      from fun _ hω => lt_of_le_of_lt hthreshold hω)).trans h
  have hfinal := hprob.trans (ENNReal.ofReal_le_ofReal (logarithmic_failure_le hlog hA hH.le))
  have hnneg : 0 ≤ (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by positivity
  dsimp only [H] at hnneg
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal

end Erdos522
