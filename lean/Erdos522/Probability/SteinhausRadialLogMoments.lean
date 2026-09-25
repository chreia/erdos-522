/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausLogarithmicMoments
import Erdos522.Probability.SteinhausOccupation
import Erdos522.Probability.CoefficientRadialValues

/-!
# Radial logarithmic moments for Steinhaus polynomials

Normalized radial coefficients transfer the uniform Fourier logarithmic
estimate to polynomial circle averages. The radian-to-circle map preserves
the normalized angular measure, and unit-modulus coefficients give exact
angular energy almost surely.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped BigOperators
namespace Erdos522

/-- Changing normalized radian angles to the unit additive circle preserves
the full coefficient-angle product law. -/
theorem measurePreserving_steinhaus_radian_circle (N : ℕ) :
    MeasurePreserving (fun q : (Fin (N + 1) → ℂ) × ℝ => (q.1, radianToUnitCircle q.2))
      ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).prod radianIntervalMeasure)
      ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).prod AddCircle.haarAddCircle) :=
  (MeasurePreserving.id _).prod measurePreserving_radianToUnitCircle

/-- Joint logarithmic moments are integrable under the actual Steinhaus law. -/
theorem integrable_normalizedSteinhaus_log_moment (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun q : (Fin (N + 1) → ℂ) × ℝ =>
      |Real.log (normalizedCoefficientValueModulus N r (q.2, q.1))| ^ p)
      ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).prod radianIntervalMeasure) := by
  have hI := (steinhaus_logarithmic_moments (normalizedRadialCoefficients N r)
    (sum_sq_norm_normalizedRadialCoefficients N r) hp).1
  have hm := ((continuous_weightedCoefficientFourier (normalizedRadialCoefficients N r)).measurable.norm.log).norm.pow_const p
  exact (measurePreserving_steinhaus_radian_circle N).integrable_comp hm.aestronglyMeasurable |>.mpr hI

/-- The radial logarithmic moment has the coefficient-uniform sixth-power bound. -/
theorem integral_normalizedSteinhaus_log_moment_le (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ a, ∫ θ, |Real.log (normalizedCoefficientValueModulus N r (θ, a))| ^ p
      ∂radianIntervalMeasure ∂Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)) ≤
        (LogMoments.amplitudeLogarithmicConstant 1 * p) ^ (6 * p) := by
  obtain ⟨hI, hbound⟩ := steinhaus_logarithmic_moments (normalizedRadialCoefficients N r)
    (sum_sq_norm_normalizedRadialCoefficients N r) hp
  have hmap := (measurePreserving_steinhaus_radian_circle N).map_eq
  have hm := ((continuous_weightedCoefficientFourier (normalizedRadialCoefficients N r)).measurable.norm.log).norm.pow_const p
  have hi := integral_map (measurePreserving_steinhaus_radian_circle N).measurable.aemeasurable
    (show AEStronglyMeasurable (fun q => |Real.log ‖weightedCoefficientFourier
      (normalizedRadialCoefficients N r) q‖| ^ p) _ by rw [hmap]; exact hm.aestronglyMeasurable)
  rw [hmap] at hi
  rw [← integral_prod _ (integrable_normalizedSteinhaus_log_moment N r hp)]
  exact hi.symm.trans_le hbound

/-- Unit-modulus coefficients make the normalized Fourier polynomial
nonzero at almost every angle. -/
theorem normalizedCoefficientValueModulus_steinhaus_ae_pos (N : ℕ) (r : ℝ) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure),
      ∀ᵐ θ ∂radianIntervalMeasure, 0 < normalizedCoefficientValueModulus N r (θ, a) := by
  filter_upwards [ae_pi_norm_steinhaus_eq_one] with a ha
  let c := fun k => normalizedRadialCoefficients N r k * a k
  have hc : ∑ k, ‖c k‖ ^ 2 = 1 := by
    simp only [c, norm_mul, ha, mul_one, sum_sq_norm_normalizedRadialCoefficients]
  have hn := measurePreserving_radianToUnitCircle.quasiMeasurePreserving.ae
    (LogMoments.fourierPolynomial_ae_ne_zero c hc (fun _ => true))
  filter_upwards [hn] with θ hθ
  apply norm_pos_iff.mpr
  simpa [LogMoments.fourierPolynomial_eq_sum, LogMoments.sign,
    normalizedCoefficientValueModulus, weightedCoefficientFourier, c] using hθ

/-- The normalized logarithm has angular `L²` sections almost surely. -/
theorem memLp_normalizedSteinhaus_log (N : ℕ) (r : ℝ) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure),
      MemLp (fun θ => Real.log (normalizedCoefficientValueModulus N r (θ, a))) 2 radianIntervalMeasure := by
  have h := (integrable_normalizedSteinhaus_log_moment N r (by norm_num : (1 : ℝ) ≤ 2)).prod_right_ae
  filter_upwards [h] with a ha
  apply (memLp_two_iff_integrable_sq
    (((measurable_normalizedCoefficientValueModulus N r).comp
      (measurable_id.prodMk measurable_const)).log.aestronglyMeasurable)).mpr
  simpa only [Real.rpow_two, sq_abs, Function.comp_def, id_eq] using ha

/-- The angular energy is one for every unit-modulus coefficient vector. -/
theorem integral_normalizedCoefficientValueModulus_sq_of_unit_modulus (N : ℕ) (r : ℝ)
    (a : Fin (N + 1) → ℂ) (ha : ∀ k, ‖a k‖ = 1) :
    (∫ θ, normalizedCoefficientValueModulus N r (θ, a) ^ 2 ∂radianIntervalMeasure) = 1 := by
  have hc : Continuous (fun θ => weightedCoefficientFourier (normalizedRadialCoefficients N r) (a, θ)) :=
    (continuous_weightedCoefficientFourier _).comp (continuous_const.prodMk continuous_id)
  have hmap := measurePreserving_radianToUnitCircle.map_eq
  have h := integral_map measurePreserving_radianToUnitCircle.measurable.aemeasurable
    (show AEStronglyMeasurable (fun θ => ‖weightedCoefficientFourier
      (normalizedRadialCoefficients N r) (a, θ)‖ ^ 2)
      (Measure.map radianToUnitCircle radianIntervalMeasure) by rw [hmap]; exact (hc.norm.pow 2).aestronglyMeasurable)
  rw [hmap, integral_norm_sq_weightedCoefficientFourier _ _ ha,
    sum_sq_norm_normalizedRadialCoefficients] at h
  exact h.symm

/-- The normalized logarithmic integral equals the Jensen circle average
minus the logarithm of the exact standard deviation. -/
theorem integral_normalizedSteinhaus_log_eq (N : ℕ) (r : ℝ) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure),
      (∫ θ, Real.log (normalizedCoefficientValueModulus N r (θ, a)) ∂radianIntervalMeasure) =
        logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) := by
  filter_upwards [normalizedCoefficientValueModulus_steinhaus_ae_pos N r, memLp_normalizedSteinhaus_log N r] with a hpos hlog
  have hi := hlog.integrable (by norm_num)
  have heq : (fun θ : ℝ => Real.log ‖(Polynomial.ofFn (N + 1) a).eval
      (r * Complex.exp (Complex.I * θ))‖) =ᵐ[radianIntervalMeasure]
      (fun θ => Real.log (normalizedCoefficientValueModulus N r (θ, a)) + Real.log (radialSigma N r)) := by
    filter_upwards [hpos] with θ hθ
    have hn : ‖(Polynomial.ofFn (N + 1) a).eval (r * Complex.exp (Complex.I * θ))‖ ≠ 0 := by
      intro hz
      rw [normalizedCoefficientValueModulus_eq, hz, zero_div] at hθ
      exact (lt_irrefl 0) hθ
    rw [normalizedCoefficientValueModulus_eq, Real.log_div hn (radialSigma_pos N r).ne']
    ring
  have hsum := integral_congr_ae heq
  rw [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_radian_polynomial_log] at hsum
  linarith

/-- Exponential level occupation agrees with normalized disk occupation. -/
theorem levelOccupation_normalizedCoefficientValueModulus_steinhaus (N : ℕ) (r t : ℝ)
    (a : Fin (N + 1) → ℂ) :
    levelOccupation radianIntervalMeasure (normalizedCoefficientValueModulus N r) (t, a) =
      SteinhausOccupation.normalizedDiskOccupation N r (Real.exp t) a := by
  unfold levelOccupation SteinhausOccupation.normalizedDiskOccupation occupation
  congr 1
  ext θ
  simp only [Set.mem_preimage]
  rw [SteinhausOccupation.mem_normalizedValueDiskEvent]
  change normalizedCoefficientValueModulus N r (θ, a) ≤ Real.exp t ↔ _
  rw [normalizedCoefficientValueModulus_eq, div_le_iff₀ (radialSigma_pos N r)]

end Erdos522
