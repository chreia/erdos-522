/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.Occupation
import Erdos522.Probability.GaussianApproximation.CircularGaussian
import Erdos522.Probability.ClippedOccupation

/-!
# Clipped logarithmic concentration for Rademacher polynomials

The exactly normalized polynomial occupation estimates imply bounded
logarithmic concentration uniformly in the clipping threshold.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Metric WithLp Set

namespace Erdos522

/-- The modulus of the exactly normalized polynomial on a circle. -/
def normalizedValueModulus (N : ℕ) (r : ℝ) (p : ℝ × LogMoments.SignVector N) : ℝ :=
  ‖realRademacherValue N r (Complex.exp (Complex.I * p.1)) p.2‖

theorem measurable_normalizedValueModulus (N : ℕ) (r : ℝ) :
    Measurable (normalizedValueModulus N r) :=
  (measurable_from_prod_countable_left fun ω =>
    (continuous_realRademacherValue_angle N r ω).measurable).norm

/-- The modulus uses the polynomial's exact finite variance, including its constant term. -/
theorem normalizedValueModulus_eq (N : ℕ) (r θ : ℝ) (ω : LogMoments.SignVector N) :
    normalizedValueModulus N r (θ, ω) =
      ‖(rademacherPolynomial N ω).eval (r * Complex.exp (Complex.I * θ))‖ / radialSigma N r := by
  unfold normalizedValueModulus
  rw [realRademacherValue_eq_polynomial]
  apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (radialSigma_pos N r).le)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, div_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Exponential occupations are the disk occupations of the normalized polynomial. -/
theorem levelOccupation_normalizedValueModulus (N : ℕ) (r s : ℝ) (ω : LogMoments.SignVector N) :
    levelOccupation radianIntervalMeasure (normalizedValueModulus N r) (s, ω) =
      normalizedDiskOccupation N r (Real.exp s) ω := by
  unfold levelOccupation normalizedDiskOccupation occupation normalizedValueDiskEvent normalizedValueModulus
  congr 1
  ext θ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_closedBall, dist_zero_right]

/-- The clipped angular logarithm of the exactly normalized polynomial. -/
def normalizedClippedLogIntegral (N : ℕ) (r T : ℝ) : LogMoments.SignVector N → ℝ :=
  clippedLogarithmicIntegral radianIntervalMeasure (normalizedValueModulus N r) T

/-- The corresponding clipped circular Gaussian expectation. -/
def circularClippedLogMean (T : ℝ) : ℝ :=
  ∫ x, clippedLogarithm T ‖x‖ ∂circularGaussian

/-- Gaussian layer cake gives the same deterministic occupation target. -/
theorem circularClippedLogMean_eq (T : ℝ) (hT : 0 ≤ T) :
    circularClippedLogMean T =
      T - ∫ s in Icc (-T) T, circularGaussian.real (closedBall 0 (Real.exp s)) := by
  have h := integral_clippedLogarithm_eq circularGaussian (fun x => ‖x‖)
    measurable_norm norm_nonneg T hT
  simpa only [circularClippedLogMean, Metric.closedBall, dist_zero_right] using h

/-- The clipped Gaussian occupation target is measurable as a function of the logarithmic level. -/
theorem measurable_circularGaussian_exp_disk :
    Measurable (fun s : ℝ => circularGaussian.real (closedBall 0 (Real.exp s))) := by
  simp_rw [circularGaussian_real_closedBall _ (Real.exp_pos _).le]
  fun_prop

/-- Mean and variance bounds for the actual normalized clipped logarithmic integral. -/
theorem exists_normalizedClippedLogIntegral_moment_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (T : ℝ) (_ : 0 ≤ T),
      |(∫ ω, normalizedClippedLogIntegral N r T ω ∂LogMoments.signMeasure N) -
        circularClippedLogMean T| ≤
          2 * T * ((valueGaussianErrorConstant C K + 1 / Real.pi) / Real.sqrt N) ∧
      variance (normalizedClippedLogIntegral N r T) (LogMoments.signMeasure N) ≤
        4 * T ^ 2 * ((valuePairGaussianErrorConstant C K + 2 * valueGaussianErrorConstant C K +
          6 / Real.pi) / Real.sqrt N) := by
  obtain ⟨C, hC, hmoment⟩ := exists_normalizedDiskOccupation_moment_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru hdegree T hT
  have hmean (s : ℝ) :
      |(∫ ω, levelOccupation radianIntervalMeasure (normalizedValueModulus N r) (s, ω)
        ∂LogMoments.signMeasure N) - circularGaussian.real (closedBall 0 (Real.exp s))| ≤
      (valueGaussianErrorConstant C K + 1 / Real.pi) / Real.sqrt N := by
    simp_rw [levelOccupation_normalizedValueModulus]
    exact (hmoment N hN K r hK hNK hrl hru hdegree (Real.exp s)).1
  have hvar (s : ℝ) :
      variance (fun ω => levelOccupation radianIntervalMeasure (normalizedValueModulus N r) (s, ω))
        (LogMoments.signMeasure N) ≤
      (valuePairGaussianErrorConstant C K + 2 * valueGaussianErrorConstant C K + 6 / Real.pi) / Real.sqrt N := by
    simp_rw [levelOccupation_normalizedValueModulus]
    exact (hmoment N hN K r hK hNK hrl hru hdegree (Real.exp s)).2
  constructor
  · rw [circularClippedLogMean_eq T hT]
    exact integral_clippedLogarithmicIntegral_error_le (LogMoments.signMeasure N) radianIntervalMeasure
      (normalizedValueModulus N r) (measurable_normalizedValueModulus N r) (fun _ => norm_nonneg _)
      T hT (fun s => circularGaussian.real (closedBall 0 (Real.exp s))) measurable_circularGaussian_exp_disk
      (fun _ => by rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one) _ hmean
  · exact variance_clippedLogarithmicIntegral_le (LogMoments.signMeasure N) radianIntervalMeasure
      (normalizedValueModulus N r) (measurable_normalizedValueModulus N r) (fun _ => norm_nonneg _)
      T hT _ hvar

/-- Clipped logarithms concentrate around the clipped circular Gaussian mean. -/
theorem exists_normalizedClippedLogIntegral_deviation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (T : ℝ) (_ : 0 ≤ T) (u : ℝ) (_ : 0 < u),
      (LogMoments.signMeasure N) {ω |
        2 * T * ((valueGaussianErrorConstant C K + 1 / Real.pi) / Real.sqrt N) + u <
          |normalizedClippedLogIntegral N r T ω - circularClippedLogMean T|} ≤
      ENNReal.ofReal (4 * T ^ 2 *
        ((valuePairGaussianErrorConstant C K + 2 * valueGaussianErrorConstant C K + 6 / Real.pi) /
          Real.sqrt N) / u ^ 2) := by
  obtain ⟨C, hC, hmoments⟩ := exists_normalizedClippedLogIntegral_moment_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru hdegree T hT u hu
  obtain ⟨hmean, hvar⟩ := hmoments N hN K r hK hNK hrl hru hdegree T hT
  have hLp : MemLp (normalizedClippedLogIntegral N r T) 2 (LogMoments.signMeasure N) :=
    MemLp.of_bound (measurable_clippedLogarithmicIntegral radianIntervalMeasure
      (normalizedValueModulus N r) (measurable_normalizedValueModulus N r) T).aestronglyMeasurable T
      (ae_of_all _ (norm_clippedLogarithmicIntegral_le radianIntervalMeasure (normalizedValueModulus N r) T hT))
  refine (measure_mono ?_).trans ((meas_ge_le_variance_div_sq hLp hu).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg u))))
  intro ω hω
  change u ≤ |normalizedClippedLogIntegral N r T ω - ∫ ω', normalizedClippedLogIntegral N r T ω' ∂LogMoments.signMeasure N|
  have htriangle := abs_sub_le (normalizedClippedLogIntegral N r T ω)
    (∫ ω', normalizedClippedLogIntegral N r T ω' ∂LogMoments.signMeasure N) (circularClippedLogMean T)
  dsimp only [Set.mem_ofPred_eq] at hω
  linarith

end Erdos522
