/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianRadialLogMoments
import Erdos522.Probability.CircularGaussianRadialEnergy
import Erdos522.Probability.LogarithmicConcentrationOnEvent

/-!
# Logarithmic concentration for circular Gaussian polynomials

Uniform logarithmic moments and angular occupation concentration control the
Jensen average. The random angular energy contributes an exponential exception.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped BigOperators ENNReal
namespace Erdos522

/-- The one-point angular occupation error coefficient. -/
def circularGaussianOccupationMeanConstant (K : ℝ) : ℝ := 10 * Real.exp (8 * K) + 1 / Real.pi

/-- The occupation variance coefficient, including all four angular exceptional sets. -/
def circularGaussianOccupationVarianceConstant (K : ℝ) : ℝ :=
  circularGaussianValuePairError K + 20 * Real.exp (8 * K) + 6 / Real.pi

/-- The Jensen logarithmic average of the actual Gaussian polynomial concentrates
with explicit clipping, moment, occupation, and energy exceptional probabilities. -/
theorem circularGaussian_logarithmic_integral_concentration (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (q : ℝ) (hq : 1 ≤ q) (T u b D : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hD : 0 < D) :
    Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian) {g |
      u + 2 * T * (circularGaussianOccupationMeanConstant K / Real.sqrt N) +
        D * Real.sqrt (Real.exp (-2 * T) + circularGaussianOccupationMeanConstant K / Real.sqrt N + b) +
        2 * Real.exp (-2 * T) <
      |logCircleAverage (Polynomial.ofFn (N+1) g) r - Real.log (radialSigma N r) - circularLogMean|} ≤
    ENNReal.ofReal (2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
      (circularGaussianOccupationVarianceConstant K / Real.sqrt N) / b ^ 2 +
      (32 * q) ^ (2 * q) / (D ^ 2) ^ q +
      4 * T ^ 2 * (circularGaussianOccupationVarianceConstant K / Real.sqrt N) / u ^ 2) := by
  let X := normalizedCoefficientValueModulus N r
  let A := {g : Fin (N + 1) → ℂ | (∫ θ, X (θ, g) ^ 2 ∂radianIntervalMeasure) ≤ 2}
  let d := circularGaussianOccupationMeanConstant K / Real.sqrt N
  let v := circularGaussianOccupationVarianceConstant K / Real.sqrt N
  have hd : 0 ≤ d := by dsimp [d, circularGaussianOccupationMeanConstant]; positivity
  have hv : 0 ≤ v := by dsimp [v, circularGaussianOccupationVarianceConstant, circularGaussianValuePairError]; positivity
  have hmean (s : ℝ) : |(∫ g, levelOccupation radianIntervalMeasure X (s, g)
      ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) - circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d := by
    simp_rw [show X = normalizedCoefficientValueModulus N r from rfl,
      levelOccupation_normalizedCoefficientValueModulus_circularGaussian]
    exact (CircularGaussianOccupation.normalizedDiskOccupation_moments N hN K r hK hNK hrl hru hdegree _).1
  have hvar (s : ℝ) : variance (fun g => levelOccupation radianIntervalMeasure X (s, g))
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) ≤ v := by
    simp_rw [show X = normalizedCoefficientValueModulus N r from rfl,
      levelOccupation_normalizedCoefficientValueModulus_circularGaussian]
    exact (CircularGaussianOccupation.normalizedDiskOccupation_moments N hN K r hK hNK hrl hru hdegree _).2
  have hp : 1 ≤ 2 * q := by linarith
  have hI := integrable_normalizedCircularGaussian_log_moment N r hp
  have hM := integral_normalizedCircularGaussian_log_moment_le N r hp
  have hlogbound := logarithmic_integral_concentration_of_energy_event
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) radianIntervalMeasure X
    (measurable_normalizedCoefficientValueModulus N r) (fun _ => norm_nonneg _)
    (normalizedCoefficientValueModulus_circularGaussian_ae_pos N r) (memLp_normalizedCircularGaussian_log N r)
    (ae_of_all _ (integrable_normalizedCoefficientValueModulus_sq N r)) A 2 (fun _ h => h)
    d v hd hv hmean hvar q hq hI.prod_right_ae hI.integral_prod_left
    ((32 * q) ^ (2 * q)) (by positivity) (by convert hM using 1; congr 1; ring)
    T u b D hT hu hb hD
  have hA : Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian) Aᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K)))) := by
    change (Measure.pi (fun _ : Fin (N+1) => circularComplexGaussian))
      {a | ¬(∫ θ, normalizedCoefficientValueModulus N r (θ,a)^2 ∂radianIntervalMeasure) ≤ 2} ≤ _
    simp only [not_le]
    exact circularGaussian_radial_energy_gt_two_le N hN K r hK hNK hrl hru
  have hbound := hlogbound.trans (add_le_add hA le_rfl)
  have hevents : {g | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
      (2 / 2 + 1) * Real.exp (-2 * T) < |∫ θ, Real.log (X (θ, g)) ∂radianIntervalMeasure - circularLogMean|}
      =ᵐ[Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)]
      {g | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
      2 * Real.exp (-2 * T) <
        |logCircleAverage (Polynomial.ofFn (N+1) g) r - Real.log (radialSigma N r) - circularLogMean|} := by
    filter_upwards [integral_normalizedCircularGaussian_log_eq N r] with g hg
    simp only [X, hg]
    norm_num
  rw [measure_congr hevents] at hbound
  refine hbound.trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end Erdos522
