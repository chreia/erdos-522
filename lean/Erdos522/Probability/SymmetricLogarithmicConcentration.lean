/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AmplitudeEnergy
import Erdos522.Probability.CoefficientRadialValues
import Erdos522.Probability.LogarithmicConcentrationRestrictedMoments

/-!
# Logarithmic concentration for bounded symmetric coefficients

The coefficient energy event supplies a nonzero Fourier polynomial and the
uniform logarithmic moments. Angular occupation is measured under the
original coefficient law, while the rare low-energy event is charged once.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Polynomial
open scoped BigOperators ENNReal
namespace Erdos522
open LogMoments

/-- Positive coefficient energy gives angular nonvanishing almost everywhere. -/
theorem weightedCoefficientFourier_ae_ne_zero {N : ℕ} (c a : Fin (N + 1) → ℂ)
    (henergy : 0 < ∑ k, ‖c k * a k‖ ^ 2) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle, weightedCoefficientFourier c (a, θ) ≠ 0 := by
  let b : Fin (N + 1) → ℂ := fun k => c k * a k
  have hp : signedPolynomial b (fun _ => true) ≠ 0 := by
    intro hp
    have hz (k : Fin (N + 1)) : b k = 0 := by
      have h := congrArg (fun P : ℂ[X] => P.coeff k.val) hp
      simpa [sign] using h
    have hh : (∑ k, ‖c k * a k‖ ^ 2) = 0 := by
      change (∑ k, ‖b k‖ ^ 2) = 0
      simp [hz]
    linarith
  have hi : Function.Injective (fun θ : AddCircle (1 : ℝ) =>
      (AddCircle.toCircle θ : ℂ)) :=
    Circle.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)
  have hfin : Set.Finite {θ : AddCircle (1 : ℝ) | fourierPolynomial b (fun _ => true) θ = 0} :=
    (Polynomial.finite_setOfPred_isRoot hp).preimage hi.injOn
  have hv : AddCircle.haarAddCircle (T := (1 : ℝ)) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  have : NullSingletonClass (volume : Measure (AddCircle (1 : ℝ))) := by
    constructor
    intro θ
    simpa using (AddCircle.volume_closedBall (1 : ℝ) (x := θ) (0 : ℝ))
  rw [ae_iff, hv]
  simpa only [not_not, fourierPolynomial_eq_sum, sign, ite_true, one_mul,
    b, weightedCoefficientFourier] using hfin.measure_zero volume

/-- Restricted coefficient-and-angle moments transport exactly from turns to radians. -/
theorem normalizedCoefficient_log_moments_on_energy {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (r B : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun q : (Fin (N + 1) → ℂ) × ℝ =>
      |Real.log (normalizedCoefficientValueModulus N r (q.2, q.1))| ^ p)
      (((Measure.pi μ).restrict (coefficientEnergyEvent (normalizedRadialCoefficients N r) B)).prod
        radianIntervalMeasure) ∧
    (∫ a in coefficientEnergyEvent (normalizedRadialCoefficients N r) B,
      ∫ θ, |Real.log (normalizedCoefficientValueModulus N r (θ, a))| ^ p
        ∂radianIntervalMeasure ∂Measure.pi μ) ≤ (amplitudeLogarithmicConstant B * p) ^ (6 * p) := by
  let A := coefficientEnergyEvent (normalizedRadialCoefficients N r) B
  let F := fun q : (Fin (N + 1) → ℂ) × AddCircle (1 : ℝ) =>
    |Real.log ‖weightedCoefficientFourier (normalizedRadialCoefficients N r) q‖| ^ p
  have hm : Measurable F := by unfold F weightedCoefficientFourier; fun_prop
  have ht := (show MeasurePreserving (fun a : Fin (N + 1) → ℂ => a)
      ((Measure.pi μ).restrict A) ((Measure.pi μ).restrict A) from
        ⟨measurable_id, Measure.map_id⟩).prod measurePreserving_radianToUnitCircle
  obtain ⟨hI, hb⟩ := symmetric_event_restricted_logarithmic_moments μ
    (normalizedRadialCoefficients N r) B hp
  change Integrable F (((Measure.pi μ).prod AddCircle.haarAddCircle).restrict (A ×ˢ univ)) at hI
  change (∫ q, F q ∂(((Measure.pi μ).prod AddCircle.haarAddCircle).restrict (A ×ˢ univ))) ≤ _ at hb
  rw [← Measure.restrict_prod_eq_prod_univ] at hI hb
  have hc := (ht.integrable_comp hm.aestronglyMeasurable).mpr hI
  refine ⟨hc, ?_⟩
  have he := integral_map ht.measurable.aemeasurable
    (f := F) (by rw [ht.map_eq]; exact hm.aestronglyMeasurable)
  rw [ht.map_eq] at he
  have hb' := he.symm.trans_le hb
  change (∫ q, (F ∘ Prod.map (fun a => a) radianToUnitCircle) q
    ∂((Measure.pi μ).restrict A).prod radianIntervalMeasure) ≤ _ at hb'
  rw [integral_prod _ hc] at hb'
  exact hb'

/-- Angular positivity is needed only on the coefficient energy event. -/
theorem normalizedCoefficientValueModulus_ae_pos_on_energy {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)] (r B : ℝ) :
    ∀ᵐ a ∂(Measure.pi μ).restrict (coefficientEnergyEvent (normalizedRadialCoefficients N r) B),
      ∀ᵐ θ ∂radianIntervalMeasure, 0 < normalizedCoefficientValueModulus N r (θ, a) := by
  filter_upwards [ae_restrict_mem (measurableSet_coefficientEnergyEvent (normalizedRadialCoefficients N r) B)]
    with a ha
  have h := measurePreserving_radianToUnitCircle.quasiMeasurePreserving.ae
    (weightedCoefficientFourier_ae_ne_zero (normalizedRadialCoefficients N r) a (by linarith [ha.1]))
  filter_upwards [h] with θ hθ
  exact norm_pos_iff.mpr hθ

/-- The normalized logarithm has angular `L²` sections on the energy event. -/
theorem memLp_normalizedCoefficient_log_on_energy {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (r B : ℝ) :
    ∀ᵐ a ∂(Measure.pi μ).restrict (coefficientEnergyEvent (normalizedRadialCoefficients N r) B),
      MemLp (fun θ => Real.log (normalizedCoefficientValueModulus N r (θ, a))) 2 radianIntervalMeasure := by
  have h := (normalizedCoefficient_log_moments_on_energy μ r B (by norm_num : (1 : ℝ) ≤ 2)).1.prod_right_ae
  filter_upwards [h] with a ha
  apply (memLp_two_iff_integrable_sq
    (((measurable_normalizedCoefficientValueModulus N r).comp
      (measurable_id.prodMk measurable_const)).log.aestronglyMeasurable)).mpr
  simpa only [Real.rpow_two, sq_abs, Function.comp_def, id_eq] using ha

/-- Exact Parseval energy for every complex coefficient vector. -/
theorem integral_normalizedCoefficientValueModulus_sq (N : ℕ) (r : ℝ) (a : Fin (N + 1) → ℂ) :
    (∫ θ, normalizedCoefficientValueModulus N r (θ, a) ^ 2 ∂radianIntervalMeasure) =
      ∑ k, ‖normalizedRadialCoefficients N r k * a k‖ ^ 2 := by
  have hc : Continuous (fun θ => weightedCoefficientFourier (normalizedRadialCoefficients N r) (a, θ)) := by
    unfold weightedCoefficientFourier
    fun_prop
  have h := integral_map measurePreserving_radianToUnitCircle.measurable.aemeasurable
    (f := fun θ => ‖weightedCoefficientFourier (normalizedRadialCoefficients N r) (a, θ)‖ ^ 2)
    (by rw [measurePreserving_radianToUnitCircle.map_eq]; exact (hc.norm.pow 2).aestronglyMeasurable)
  rw [measurePreserving_radianToUnitCircle.map_eq] at h
  have hp := integral_norm_sq_fourierPolynomial
    (fun k => normalizedRadialCoefficients N r k * a k) (fun _ => true)
  simp only [fourierPolynomial_eq_sum, sign, ite_true, one_mul] at hp
  exact h.symm.trans hp

/-- On the energy event, the normalized logarithmic integral is the Jensen average minus `log σ`. -/
theorem integral_normalizedCoefficient_log_eq_on_energy {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (r B : ℝ) :
    ∀ᵐ a ∂(Measure.pi μ).restrict (coefficientEnergyEvent (normalizedRadialCoefficients N r) B),
      (∫ θ, Real.log (normalizedCoefficientValueModulus N r (θ, a)) ∂radianIntervalMeasure) =
        logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) := by
  filter_upwards [normalizedCoefficientValueModulus_ae_pos_on_energy μ r B,
    memLp_normalizedCoefficient_log_on_energy μ r B] with a hpos hlog
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

/-- The amplitude logarithmic constant is positive for every real bound. -/
theorem amplitude_logarithmic_constant_pos (B : ℝ) : 0 < amplitudeLogarithmicConstant B := by
  have hmax : 0 ≤ max ((1 / 2 : ℝ) * Real.log 2) (Real.log B) :=
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))).trans (le_max_left _ _)
  unfold amplitudeLogarithmicConstant
  linarith [rademacherLogarithmicConstant_pos]

/-- Actual bounded centrally symmetric coefficients satisfy logarithmic
concentration from their unconditioned occupation moments. All logarithmic
moment and nonvanishing assumptions are discharged on the energy event. -/
theorem symmetric_logarithmic_integral_concentration (N : ℕ) (hN : 0 < N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (K r B : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) (hB : 0 < B)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hsecond : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1)
    (d v : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hmean : ∀ s, |(∫ a, levelOccupation radianIntervalMeasure
        (normalizedCoefficientValueModulus N r) (s, a) ∂Measure.pi μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d)
    (hvar : ∀ s, variance (fun a => levelOccupation radianIntervalMeasure
        (normalizedCoefficientValueModulus N r) (s, a)) (Measure.pi μ) ≤ v)
    (q : ℝ) (hq : 1 ≤ q) (T u b D : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hD : 0 < D) :
    (Measure.pi μ) {a | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B ^ 2 / 2 + 1) * Real.exp (-2 * T) <
      |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ) / (2 * B ^ 4 * Real.exp (6 * K))) +
        v / b ^ 2 + (amplitudeLogarithmicConstant B * (2 * q)) ^ (12 * q) / (D ^ 2) ^ q +
        4 * T ^ 2 * v / u ^ 2) := by
  let X := normalizedCoefficientValueModulus N r
  let A := coefficientEnergyEvent (normalizedRadialCoefficients N r) B
  have hA : MeasurableSet A := measurableSet_coefficientEnergyEvent _ _
  have hmoment := normalizedCoefficient_log_moments_on_energy μ r B (by linarith : 1 ≤ 2 * q)
  have hM0 : 0 ≤ (amplitudeLogarithmicConstant B * (2 * q)) ^ (6 * (2 * q)) :=
    Real.rpow_nonneg (mul_nonneg (amplitude_logarithmic_constant_pos B).le (by linarith)) _
  have hbnd := logarithmic_integral_concentration_restricted_moments (Measure.pi μ)
    radianIntervalMeasure X (measurable_normalizedCoefficientValueModulus N r) (fun _ => norm_nonneg _)
    A hA (normalizedCoefficientValueModulus_ae_pos_on_energy μ r B)
    (memLp_normalizedCoefficient_log_on_energy μ r B)
    (ae_of_all _ (integrable_normalizedCoefficientValueModulus_sq N r))
    (B ^ 2) (fun a ha => by
      rw [show X = normalizedCoefficientValueModulus N r from rfl,
        integral_normalizedCoefficientValueModulus_sq]
      exact ha.2)
    d v hd hv hmean hvar q hq hmoment.1.prod_right_ae hmoment.1.integral_prod_left
    ((amplitudeLogarithmicConstant B * (2 * q)) ^ (6 * (2 * q))) hM0 hmoment.2
    T u b D hT hu hb hD
  have heq : {a | a ∈ A ∧ u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B ^ 2 / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, a)) ∂radianIntervalMeasure) - circularLogMean|}
      =ᵐ[Measure.pi μ] {a | a ∈ A ∧ u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B ^ 2 / 2 + 1) * Real.exp (-2 * T) <
      |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} := by
    filter_upwards [(ae_restrict_iff' hA).mp (integral_normalizedCoefficient_log_eq_on_energy μ r B)]
      with a ha
    by_cases hmem : a ∈ A
    · simp only [hmem, true_and, X, ha hmem]
    · simp only [hmem, false_and]
  rw [measure_congr heq] at hbnd
  have hcompl : (Measure.pi μ) Aᶜ ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ) / (2 * B ^ 4 * Real.exp (6 * K)))) := by
    rw [← ofReal_measureReal (μ := Measure.pi μ)]
    exact ENNReal.ofReal_le_ofReal
      (measure_compl_radial_coefficientEnergyEvent_le N hN μ K r hK hNK hrl hru hB hbound hsecond)
  have hsub : {a | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B ^ 2 / 2 + 1) * Real.exp (-2 * T) <
      |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} ⊆
      Aᶜ ∪ {a | a ∈ A ∧ u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B ^ 2 / 2 + 1) * Real.exp (-2 * T) <
      |logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) - circularLogMean|} := by
    intro a ha
    by_cases hm : a ∈ A
    · exact Or.inr ⟨hm, ha⟩
    · exact Or.inl hm
  have h := (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hcompl hbnd))
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
  congr 1
  rw [show (6 * (2 * q)) = 12 * q by ring]
  ring

end Erdos522
