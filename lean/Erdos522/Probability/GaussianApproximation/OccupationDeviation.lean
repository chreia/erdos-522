/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.Occupation
import Erdos522.Probability.GaussianApproximation.CircularGaussian

/-!
# Small-value occupation deviations

The Gaussian disk law and occupation variance give the first exceptional
event in logarithmic unclipping, with its explicit Chebyshev budget.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Metric

namespace Erdos522

/-- The circular Gaussian mass of a disk is at most its squared radius. -/
theorem circularGaussian_real_closedBall_le_sq (t : ℝ) (ht : 0 ≤ t) :
    circularGaussian.real (closedBall 0 t) ≤ t ^ 2 := by
  rw [circularGaussian_real_closedBall t ht]
  linarith [Real.add_one_le_exp (-t ^ 2)]

/-- Small-value occupation exceeds its Gaussian scale only on the displayed Chebyshev event. -/
theorem exists_normalizedDiskOccupation_deviation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (T b : ℝ) (_ : 0 < b),
      (LogMoments.signMeasure N) {ω |
        Real.exp (-2 * T) + (valueGaussianErrorConstant C K + 1 / Real.pi) / Real.sqrt N + b <
          normalizedDiskOccupation N r (Real.exp (-T)) ω} ≤
      ENNReal.ofReal (
        ((valuePairGaussianErrorConstant C K + 2 * valueGaussianErrorConstant C K + 6 / Real.pi) /
          Real.sqrt N) / b ^ 2) := by
  obtain ⟨C, hC, hmoments⟩ := exists_normalizedDiskOccupation_moment_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru hdegree T b hb
  obtain ⟨hmean, hvar⟩ := hmoments N hN K r hK hNK hrl hru hdegree (Real.exp (-T))
  have hgauss := circularGaussian_real_closedBall_le_sq (Real.exp (-T)) (Real.exp_pos _).le
  have heq : Real.exp (-T) ^ 2 = Real.exp (-2 * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hgauss
  have hLp : MemLp (normalizedDiskOccupation N r (Real.exp (-T))) 2 (LogMoments.signMeasure N) :=
    memLp_occupation (LogMoments.signMeasure N) radianIntervalMeasure
      (measurableSet_normalizedValueDiskEvent N r (Real.exp (-T))) 2
  refine (measure_mono ?_).trans ((meas_ge_le_variance_div_sq hLp hb).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg b))))
  intro ω hω
  change b ≤ |normalizedDiskOccupation N r (Real.exp (-T)) ω -
    ∫ ω', normalizedDiskOccupation N r (Real.exp (-T)) ω' ∂LogMoments.signMeasure N|
  have hupper := (abs_le.mp hmean).2
  have habs := le_abs_self (normalizedDiskOccupation N r (Real.exp (-T)) ω -
    ∫ ω', normalizedDiskOccupation N r (Real.exp (-T)) ω' ∂LogMoments.signMeasure N)
  dsimp only [Set.mem_ofPred_eq] at hω
  linarith

end Erdos522
