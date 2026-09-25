/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausRadialLogMoments
import Erdos522.Probability.LogarithmicConcentrationOnEvent

/-!
# Logarithmic circle concentration for Steinhaus polynomials

The uniform logarithmic moments and two-point occupation estimates combine
with the exact angular energy to concentrate the Jensen circle average.
All radii use the actual finite product coefficient law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace Erdos522

/-- A finite constant dominating both occupation errors. -/
def steinhausOccupationConstant (C K : ℝ) : ℝ :=
  1 + |circularValueGaussianErrorConstant C K| +
    |circularValuePairGaussianErrorConstant C K + 2 * circularValueGaussianErrorConstant C K + 4 / Real.pi|

theorem steinhausOccupationConstant_pos (C K : ℝ) : 0 < steinhausOccupationConstant C K := by
  unfold steinhausOccupationConstant
  positivity

theorem steinhausLogarithmicConstant_pos :
    0 < LogMoments.amplitudeLogarithmicConstant 1 := by
  unfold LogMoments.amplitudeLogarithmicConstant
  have h := LogMoments.rademacherLogarithmicConstant_pos
  have hm : 0 ≤ max ((1 / 2 : ℝ) * Real.log 2) (Real.log 1) := by
    simpa only [Real.log_one] using le_max_right ((1 / 2 : ℝ) * Real.log 2) 0
  linarith

/-- Quantitative logarithmic concentration under the actual Steinhaus
coefficient law, with exact sixth-power moment and clipping terms. -/
theorem exists_steinhaus_logarithmic_concentration_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (q : ℝ) (_ : 1 ≤ q) (T u b D : ℝ) (_ : 0 ≤ T) (_ : 0 < u) (_ : 0 < b) (_ : 0 < D),
      let d := steinhausOccupationConstant C K / Real.sqrt N
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)) {a |
        u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
          (3 / 2 : ℝ) * Real.exp (-2 * T) <
        |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} ≤
        ENNReal.ofReal (d / b ^ 2 + (LogMoments.amplitudeLogarithmicConstant 1 * (2 * q)) ^ (12 * q) /
          (D ^ 2) ^ q + 4 * T ^ 2 * d / u ^ 2) := by
  obtain ⟨C, hC, hocc⟩ := SteinhausOccupation.exists_normalizedDiskOccupation_moment_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru hdegree q hq T u b D hT hu hb hD
  let μ := Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)
  let X := normalizedCoefficientValueModulus N r
  let A := {a : Fin (N + 1) → ℂ | ∀ k, ‖a k‖ = 1}
  let H := steinhausOccupationConstant C K
  let d := H / Real.sqrt N
  have hd : 0 ≤ d := div_nonneg (steinhausOccupationConstant_pos C K).le (Real.sqrt_nonneg _)
  have hmean : ∀ s, |(∫ a, levelOccupation radianIntervalMeasure X (s, a) ∂μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d := by
    intro s
    simp_rw [show X = normalizedCoefficientValueModulus N r from rfl,
      levelOccupation_normalizedCoefficientValueModulus_steinhaus]
    refine (hocc N hN K r hK hNK hrl hru hdegree (Real.exp s)).1.trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    dsimp only [H, steinhausOccupationConstant]
    linarith [le_abs_self (circularValueGaussianErrorConstant C K),
      abs_nonneg (circularValuePairGaussianErrorConstant C K + 2 * circularValueGaussianErrorConstant C K + 4 / Real.pi)]
  have hvar : ∀ s, variance (fun a => levelOccupation radianIntervalMeasure X (s, a)) μ ≤ d := by
    intro s
    simp_rw [show X = normalizedCoefficientValueModulus N r from rfl,
      levelOccupation_normalizedCoefficientValueModulus_steinhaus]
    refine (hocc N hN K r hK hNK hrl hru hdegree (Real.exp s)).2.trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    dsimp only [H, steinhausOccupationConstant]
    linarith [le_abs_self (circularValuePairGaussianErrorConstant C K + 2 * circularValueGaussianErrorConstant C K + 4 / Real.pi),
      abs_nonneg (circularValueGaussianErrorConstant C K)]
  have hp : 1 ≤ 2 * q := by linarith
  have hI := integrable_normalizedSteinhaus_log_moment N r hp
  have hM := integral_normalizedSteinhaus_log_moment_le N r hp
  have hlogbound := logarithmic_integral_concentration_of_energy_event μ radianIntervalMeasure X
    (measurable_normalizedCoefficientValueModulus N r) (fun _ => norm_nonneg _)
    (normalizedCoefficientValueModulus_steinhaus_ae_pos N r) (memLp_normalizedSteinhaus_log N r)
    (ae_of_all _ (integrable_normalizedCoefficientValueModulus_sq N r)) A 1
    (fun a ha => (integral_normalizedCoefficientValueModulus_sq_of_unit_modulus N r a ha).le)
    d d hd hd hmean hvar q hq hI.prod_right_ae hI.integral_prod_left
    ((LogMoments.amplitudeLogarithmicConstant 1 * (2 * q)) ^ (12 * q))
    (Real.rpow_nonneg (mul_nonneg steinhausLogarithmicConstant_pos.le (by linarith)) _)
    (by convert hM using 1; congr 1; ring) T u b D hT hu hb hD
  have hA : μ Aᶜ = 0 := by
    exact ae_iff.mp (show ∀ᵐ a ∂μ, a ∈ A from ae_pi_norm_steinhaus_eq_one)
  rw [hA, zero_add] at hlogbound
  have hevents : {a | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
      (1 / 2 + 1) * Real.exp (-2 * T) < |∫ θ, Real.log (X (θ, a)) ∂radianIntervalMeasure - circularLogMean|}
      =ᵐ[μ] {a | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (3 / 2 : ℝ) * Real.exp (-2 * T) <
      |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} := by
    filter_upwards [integral_normalizedSteinhaus_log_eq N r] with a ha
    simp only [X, ha]
    norm_num
  rw [measure_congr hevents] at hlogbound
  exact hlogbound

end Erdos522
