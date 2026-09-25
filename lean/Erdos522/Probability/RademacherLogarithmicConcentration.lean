/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.DistributionBound
import Erdos522.Probability.LogarithmicConcentration
import Erdos522.Analysis.JensenSecants

/-!
# Logarithmic integral concentration for Rademacher polynomials

Exact variance normalization identifies each radial polynomial with a finite
Rademacher Fourier sum. Harmonic restriction supplies its uniform logarithmic
moments, and occupation concentration controls its logarithmic circle average.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Polynomial
open scoped BigOperators
namespace Erdos522
open LogMoments

/-- The deterministic coefficients of a polynomial normalized by its exact
radial standard deviation. -/
def normalizedRadialCoefficients (N : ℕ) (r : ℝ) (k : Fin (N + 1)) : ℂ :=
  (r : ℂ) ^ k.val / (radialSigma N r : ℂ)

/-- The normalized radial coefficient vector has squared norm exactly one. -/
theorem sum_sq_norm_normalizedRadialCoefficients (N : ℕ) (r : ℝ) :
    ∑ k, ‖normalizedRadialCoefficients N r k‖ ^ 2 = 1 := by
  simp only [normalizedRadialCoefficients, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (radialSigma_pos N r), div_pow, ← pow_mul,
    Nat.mul_comm _ 2, even_two_mul, Even.pow_abs, radialSigma_sq]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k => r ^ (2 * k))]
  change radialVariance N r / radialVariance N r = 1
  exact div_self (radialVariance_pos N r).ne'

/-- Conversion from real radian representatives to the additive circle in turns. -/
def radianToUnitCircle (θ : ℝ) : AddCircle (1 : ℝ) :=
  AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
    (θ : AddCircle (2 * Real.pi))

theorem radianToUnitCircle_eq (θ : ℝ) :
    radianToUnitCircle θ = ((θ / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
  simp only [radianToUnitCircle, AddCircle.equivAddCircle_apply_mk, mul_one, div_eq_mul_inv]

/-- Radian-to-turn conversion preserves normalized angular measure. -/
theorem measurePreserving_radianToUnitCircle :
    MeasurePreserving radianToUnitCircle radianIntervalMeasure AddCircle.haarAddCircle := by
  let e := AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  have he : MeasurePreserving e radianHaar AddCircle.haarAddCircle :=
    e.toAddMonoidHom.measurePreserving (AddCircle.continuous_equivAddCircle _ _ _ _)
      e.surjective (by simp)
  exact he.comp measurePreserving_radianQuotient

/-- The complex phase has its usual radian normalization. -/
theorem toCircle_radianToUnitCircle (θ : ℝ) :
    (AddCircle.toCircle (radianToUnitCircle θ) : ℂ) = Complex.exp (Complex.I * θ) := by
  rw [radianToUnitCircle_eq]
  simp only [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
  congr 1
  push_cast
  field_simp

/-- The radial Fourier sum is exactly the normalized polynomial value. -/
theorem radial_fourierPolynomial_eq (N : ℕ) (r θ : ℝ) (ω : SignVector N) :
    fourierPolynomial (normalizedRadialCoefficients N r) ω (radianToUnitCircle θ) =
      (rademacherPolynomial N ω).eval (r * Complex.exp (Complex.I * θ)) / radialSigma N r := by
  simp only [fourierPolynomial, signedPolynomial, eval_finsetSum, eval_monomial,
    normalizedRadialCoefficients, toCircle_radianToUnitCircle, rademacherPolynomial_eval,
    Finset.sum_div, mul_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The actual normalized value modulus is the radial Fourier modulus. -/
theorem normalizedValueModulus_eq_fourier (N : ℕ) (r θ : ℝ) (ω : SignVector N) :
    normalizedValueModulus N r (θ, ω) =
      ‖fourierPolynomial (normalizedRadialCoefficients N r) ω (radianToUnitCircle θ)‖ := by
  rw [radial_fourierPolynomial_eq, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radialSigma_pos N r), normalizedValueModulus_eq]

/-- Every sign vector has strictly positive probability in the finite product law. -/
theorem signMeasure_singleton_ne_zero (N : ℕ) (ω : SignVector N) : signMeasure N {ω} ≠ 0 := by
  simp [signMeasure, Measure.pi_singleton,
    PMF.uniformOfFintype_apply]

/-- Integrability of an angular moment follows for every finite sign vector. -/
theorem integrable_normalizedValue_log_moment_section {C : ℝ} (hC : 1 ≤ C)
    (hR : HarmonicL2Restriction C) (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p)
    (ω : SignVector N) :
    Integrable (fun θ => |Real.log (normalizedValueModulus N r (θ, ω))| ^ p)
      radianIntervalMeasure := by
  have hI := (uniform_logarithmic_moments_of_harmonic_restriction hC hR
    (normalizedRadialCoefficients N r) (sum_sq_norm_normalizedRadialCoefficients N r) hp).1
  have hsection := ae_iff_of_countable.mp hI.prod_right_ae ω (signMeasure_singleton_ne_zero N ω)
  have hm := (((continuous_fourierPolynomial (normalizedRadialCoefficients N r) ω).measurable.norm.log).norm.pow_const p)
  have h := (measurePreserving_radianToUnitCircle.integrable_comp hm.aestronglyMeasurable).mpr hsection
  simpa only [Real.norm_eq_abs, normalizedValueModulus_eq_fourier, Function.comp_def,
    randomFourier] using h

/-- The expected angular moment retains the coefficient-uniform Fourier bound. -/
theorem integral_normalizedValue_log_moment_le {C : ℝ} (hC : 1 ≤ C)
    (hR : HarmonicL2Restriction C) (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ ω, ∫ θ, |Real.log (normalizedValueModulus N r (θ, ω))| ^ p
      ∂radianIntervalMeasure ∂signMeasure N) ≤ (fourierLogarithmicConstant C * p) ^ (6 * p) := by
  obtain ⟨hI, hbound⟩ := uniform_logarithmic_moments_of_harmonic_restriction hC hR
    (normalizedRadialCoefficients N r) (sum_sq_norm_normalizedRadialCoefficients N r) hp
  rw [fourierMeasure, integral_prod _ hI] at hbound
  apply hbound.trans_eq'
  apply integral_congr_ae
  filter_upwards with ω
  have hm := (((continuous_fourierPolynomial (normalizedRadialCoefficients N r) ω).measurable.norm.log).norm.pow_const p)
  have hmap := measurePreserving_radianToUnitCircle.map_eq
  have h := integral_map measurePreserving_radianToUnitCircle.measurable.aemeasurable
    (show AEStronglyMeasurable (fun θ => |Real.log ‖fourierPolynomial
      (normalizedRadialCoefficients N r) ω θ‖| ^ p)
      (Measure.map radianToUnitCircle radianIntervalMeasure) by
        rw [hmap]; simpa only [Real.norm_eq_abs] using hm.aestronglyMeasurable)
  rw [hmap] at h
  simpa only [normalizedValueModulus_eq_fourier, randomFourier] using h

/-- The normalized modulus is positive almost everywhere for each sign vector. -/
theorem normalizedValueModulus_ae_pos (N : ℕ) (r : ℝ) (ω : SignVector N) :
    ∀ᵐ θ ∂radianIntervalMeasure, 0 < normalizedValueModulus N r (θ, ω) := by
  have h := measurePreserving_radianToUnitCircle.quasiMeasurePreserving.ae
    (fourierPolynomial_ae_ne_zero (normalizedRadialCoefficients N r)
      (sum_sq_norm_normalizedRadialCoefficients N r) ω)
  filter_upwards [h] with θ hθ
  rw [normalizedValueModulus_eq_fourier]
  exact norm_pos_iff.mpr hθ

/-- Parseval gives unit energy for every sign vector and every real radius. -/
theorem integral_normalizedValueModulus_sq (N : ℕ) (r : ℝ) (ω : SignVector N) :
    (∫ θ, normalizedValueModulus N r (θ, ω) ^ 2 ∂radianIntervalMeasure) = 1 := by
  have hm : AEStronglyMeasurable (fun θ => ‖fourierPolynomial (normalizedRadialCoefficients N r) ω θ‖ ^ 2) AddCircle.haarAddCircle :=
    ((continuous_fourierPolynomial (normalizedRadialCoefficients N r) ω).norm.pow 2).aestronglyMeasurable
  have hmap := measurePreserving_radianToUnitCircle.map_eq
  have h := integral_map measurePreserving_radianToUnitCircle.measurable.aemeasurable
    (show AEStronglyMeasurable (fun θ => ‖fourierPolynomial
      (normalizedRadialCoefficients N r) ω θ‖ ^ 2)
      (Measure.map radianToUnitCircle radianIntervalMeasure) by rwa [hmap])
  rw [hmap, integral_norm_sq_fourierPolynomial, sum_sq_norm_normalizedRadialCoefficients] at h
  simpa only [normalizedValueModulus_eq_fourier] using h.symm

/-- Squared normalized values are angularly integrable pathwise. -/
theorem integrable_normalizedValueModulus_sq (N : ℕ) (r : ℝ) (ω : SignVector N) :
    Integrable (fun θ => normalizedValueModulus N r (θ, ω) ^ 2) radianIntervalMeasure := by
  have hc := continuous_fourierPolynomial (normalizedRadialCoefficients N r) ω
  have hI : Integrable (fun θ => ‖fourierPolynomial (normalizedRadialCoefficients N r) ω θ‖ ^ 2)
      AddCircle.haarAddCircle :=
    (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := (measurePreserving_radianToUnitCircle.integrable_comp
    (hc.norm.pow 2).aestronglyMeasurable).mpr hI
  simpa only [normalizedValueModulus_eq_fourier, Function.comp_def, Pi.pow_apply] using h

/-- The normalized angular logarithm belongs to `L²` for every sign vector. -/
theorem memLp_normalizedValue_log {C : ℝ} (hC : 1 ≤ C) (hR : HarmonicL2Restriction C)
    (N : ℕ) (r : ℝ) (ω : SignVector N) :
    MemLp (fun θ => Real.log (normalizedValueModulus N r (θ, ω))) 2 radianIntervalMeasure := by
  have hm : Measurable (fun θ => Real.log (normalizedValueModulus N r (θ, ω))) :=
    ((measurable_normalizedValueModulus N r).comp (measurable_id.prodMk measurable_const)).log
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have h := integrable_normalizedValue_log_moment_section hC hR N r (by norm_num : (1 : ℝ) ≤ 2) ω
  simpa only [Real.rpow_two, sq_abs] using h

/-- Normalized radian integration is the standard circle average. -/
theorem integral_radian_polynomial_log (P : ℂ[X]) (r : ℝ) :
    (∫ θ, Real.log ‖P.eval (r * Complex.exp (Complex.I * θ))‖ ∂radianIntervalMeasure) =
      logCircleAverage P r := by
  rw [radianIntervalMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    logCircleAverage, Real.circleAverage_def,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp only [one_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with θ
  simp only [circleMap, zero_add, mul_comm Complex.I (θ : ℂ)]

/-- The normalized logarithmic integral is Jensen's logarithmic circle average
minus the exact standard-deviation logarithm. -/
theorem integral_normalizedValue_log_eq {C : ℝ} (hC : 1 ≤ C) (hR : HarmonicL2Restriction C)
    (N : ℕ) (r : ℝ) (ω : SignVector N) :
    (∫ θ, Real.log (normalizedValueModulus N r (θ, ω)) ∂radianIntervalMeasure) =
      logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) := by
  have hi := (memLp_normalizedValue_log hC hR N r ω).integrable (by norm_num)
  have heq : (fun θ : ℝ => Real.log ‖(rademacherPolynomial N ω).eval
      (r * Complex.exp (Complex.I * θ))‖) =ᵐ[radianIntervalMeasure]
      (fun θ => Real.log (normalizedValueModulus N r (θ, ω)) + Real.log (radialSigma N r)) := by
    filter_upwards [normalizedValueModulus_ae_pos N r ω] with θ hθ
    have hn : ‖(rademacherPolynomial N ω).eval (r * Complex.exp (Complex.I * θ))‖ ≠ 0 := by
      intro hz
      rw [normalizedValueModulus_eq, hz, zero_div] at hθ
      exact (lt_irrefl 0) hθ
    rw [normalizedValueModulus_eq, Real.log_div hn (radialSigma_pos N r).ne']
    ring
  have hsum := integral_congr_ae heq
  rw [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_radian_polynomial_log] at hsum
  linarith

/-- One finite constant dominates both normalized occupation errors. Its
first argument is the existential universal constant supplied by Bentkus. -/
def rademacherOccupationConstant (C K : ℝ) : ℝ :=
  1 + |valueGaussianErrorConstant C K + 1 / Real.pi| +
    |valuePairGaussianErrorConstant C K + 2 * valueGaussianErrorConstant C K + 6 / Real.pi|

theorem rademacherOccupationConstant_pos (C K : ℝ) : 0 < rademacherOccupationConstant C K := by
  unfold rademacherOccupationConstant
  positivity

/-- Conditional harmonic restriction and the actual occupation estimates give
an explicit finite logarithmic concentration bound. -/
theorem exists_rademacher_logarithmic_concentration_constant {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (q : ℝ) (_ : 1 ≤ q) (T u b D : ℝ) (_ : 0 ≤ T) (_ : 0 < u) (_ : 0 < b) (_ : 0 < D),
      let d := rademacherOccupationConstant B K / Real.sqrt N
      (signMeasure N) {ω | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
          (3 / 2 : ℝ) * Real.exp (-2 * T) <
        |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|} ≤
        ENNReal.ofReal (d / b ^ 2 + (fourierLogarithmicConstant C * (2 * q)) ^ (12 * q) /
          (D ^ 2) ^ q + 4 * T ^ 2 * d / u ^ 2) := by
  obtain ⟨B, hB, hocc⟩ := exists_normalizedDiskOccupation_moment_constant
  refine ⟨B, hB, ?_⟩
  intro N hN K r hK hNK hrl hru hdegree q hq T u b D hT hu hb hD
  let H := rademacherOccupationConstant B K
  let d := H / Real.sqrt N
  have hd : 0 ≤ d := div_nonneg (rademacherOccupationConstant_pos B K).le (Real.sqrt_nonneg _)
  have hmean : ∀ s, |(∫ ω, levelOccupation radianIntervalMeasure
      (normalizedValueModulus N r) (s, ω) ∂signMeasure N) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d := by
    intro s
    simp_rw [levelOccupation_normalizedValueModulus]
    refine (hocc N hN K r hK hNK hrl hru hdegree (Real.exp s)).1.trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    dsimp only [H, rademacherOccupationConstant]
    linarith [le_abs_self (valueGaussianErrorConstant B K + 1 / Real.pi),
      abs_nonneg (valuePairGaussianErrorConstant B K + 2 * valueGaussianErrorConstant B K + 6 / Real.pi)]
  have hvar : ∀ s, variance (fun ω => levelOccupation radianIntervalMeasure
      (normalizedValueModulus N r) (s, ω)) (signMeasure N) ≤ d := by
    intro s
    simp_rw [levelOccupation_normalizedValueModulus]
    refine (hocc N hN K r hK hNK hrl hru hdegree (Real.exp s)).2.trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    dsimp only [H, rademacherOccupationConstant]
    linarith [le_abs_self (valuePairGaussianErrorConstant B K + 2 * valueGaussianErrorConstant B K + 6 / Real.pi),
      abs_nonneg (valueGaussianErrorConstant B K + 1 / Real.pi)]
  have hp : 1 ≤ 2 * q := by linarith
  have hmoment := integral_normalizedValue_log_moment_le hC hR N r hp
  have h := logarithmic_integral_concentration (signMeasure N) radianIntervalMeasure
    (normalizedValueModulus N r) (measurable_normalizedValueModulus N r)
    (fun _ => norm_nonneg _) (normalizedValueModulus_ae_pos N r)
    (memLp_normalizedValue_log hC hR N r) (integrable_normalizedValueModulus_sq N r)
    1 (fun ω => (integral_normalizedValueModulus_sq N r ω).le) d d hd hd hmean hvar q hq
    (fun ω => integrable_normalizedValue_log_moment_section hC hR N r hp ω)
    Integrable.of_finite ((fourierLogarithmicConstant C * (2 * q)) ^ (12 * q))
    (Real.rpow_nonneg (mul_nonneg (fourierLogarithmicConstant_pos hC).le (by linarith)) _)
    (by convert hmoment using 1; congr 1; ring) T u b D hT hu hb hD
  simpa only [integral_normalizedValue_log_eq hC hR, show (1 / 2 + 1 : ℝ) = 3 / 2 by norm_num] using h

end Erdos522
