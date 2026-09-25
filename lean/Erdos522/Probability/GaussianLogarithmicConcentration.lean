/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianOccupation
import Erdos522.Probability.GaussianRadialEnergy
import Erdos522.Probability.LogarithmicConcentrationOnEvent

/-!
# Logarithmic integral concentration for Gaussian polynomials

Exactly normalized Gaussian values have uniform logarithmic moments of order
one. Their occupation estimates and exponentially likely angular-energy
bound give quantitative concentration of the Jensen logarithmic average.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped BigOperators ENNReal
namespace Erdos522

/-- The exactly normalized modulus on radian angle and Gaussian coefficient space. -/
def normalizedGaussianValueModulus (N : ℕ) (r : ℝ) (p : ℝ × (Fin (N + 1) → ℝ)) : ℝ :=
  ‖gaussianFourierPolynomial (normalizedRadialCoefficients N r) p.2 (radianToUnitCircle p.1)‖

@[fun_prop]
theorem measurable_normalizedGaussianValueModulus (N : ℕ) (r : ℝ) :
    Measurable (normalizedGaussianValueModulus N r) := by
  unfold normalizedGaussianValueModulus
  have hm : Measurable radianToUnitCircle := by unfold radianToUnitCircle; fun_prop
  exact ((measurable_gaussianFourierPolynomial (normalizedRadialCoefficients N r)).comp
    (measurable_snd.prodMk (hm.comp measurable_fst))).norm

theorem normalizedGaussianValueModulus_eq (N : ℕ) (r θ : ℝ) (g : Fin (N + 1) → ℝ) :
    normalizedGaussianValueModulus N r (θ, g) =
      ‖(gaussianPolynomial N g).eval (r * Complex.exp (Complex.I * θ))‖ / radialSigma N r := by
  simp only [normalizedGaussianValueModulus, gaussianFourierPolynomial_radial_eq,
    toCircle_radianToUnitCircle, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radialSigma_pos N r)]

/-- Joint Gaussian logarithmic moments are integrable in coefficients and normalized radian angle. -/
theorem integrable_normalizedGaussian_log_moment (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun q : (Fin (N + 1) → ℝ) × ℝ =>
      |Real.log (normalizedGaussianValueModulus N r (q.2, q.1))| ^ p)
      ((gaussianCoefficientMeasure (N + 1)).prod radianIntervalMeasure) := by
  have hm : Measurable (fun q : (Fin (N + 1) → ℝ) × ℝ =>
      |Real.log (normalizedGaussianValueModulus N r (q.2, q.1))| ^ p) :=
    ((measurable_normalizedGaussianValueModulus N r).comp measurable_swap).log.norm.pow_const p
  have hsection (θ : ℝ) := gaussian_logarithmic_moments
    (fun k => normalizedRadialCoefficients N r k * (AddCircle.toCircle (radianToUnitCircle θ) : ℂ) ^ k.val)
    (by rw [sum_sq_norm_fourier_phases, sum_sq_norm_normalizedRadialCoefficients]) hp
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun θ => (hsection θ).1
  · apply (integrable_const ((16 * p) ^ p)).mono'
    · exact hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    · filter_upwards with θ
      have hn (g : Fin (N + 1) → ℝ) : 0 ≤ |Real.log (normalizedGaussianValueModulus N r (θ, g))| ^ p :=
        Real.rpow_nonneg (abs_nonneg _) _
      simp only [Real.norm_eq_abs]
      simp_rw [abs_of_nonneg (hn _)]
      rw [abs_of_nonneg (integral_nonneg_of_ae (ae_of_all _ hn))]
      exact (hsection θ).2

/-- The uniform Gaussian logarithmic moment retains the explicit constant `16`. -/
theorem integral_normalizedGaussian_log_moment_le (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ g, ∫ θ, |Real.log (normalizedGaussianValueModulus N r (θ, g))| ^ p
      ∂radianIntervalMeasure ∂gaussianCoefficientMeasure (N + 1)) ≤ (16 * p) ^ p := by
  have hI := integrable_normalizedGaussian_log_moment N r hp
  rw [integral_integral_swap hI]
  calc
    _ ≤ ∫ _ : ℝ, (16 * p) ^ p ∂radianIntervalMeasure := by
      apply integral_mono hI.integral_prod_right (integrable_const _)
      intro θ
      exact (gaussian_logarithmic_moments
        (fun k => normalizedRadialCoefficients N r k * (AddCircle.toCircle (radianToUnitCircle θ) : ℂ) ^ k.val)
        (by rw [sum_sq_norm_fourier_phases, sum_sq_norm_normalizedRadialCoefficients]) hp).2
    _ = _ := by simp

/-- Normalized Gaussian values are positive for almost every coefficient vector and angle. -/
theorem normalizedGaussianValueModulus_ae_pos (N : ℕ) (r : ℝ) :
    ∀ᵐ g ∂gaussianCoefficientMeasure (N + 1), ∀ᵐ θ ∂radianIntervalMeasure,
      0 < normalizedGaussianValueModulus N r (θ, g) := by
  have hset : MeasurableSet {p : ℝ × (Fin (N + 1) → ℝ) |
      0 < normalizedGaussianValueModulus N r (p.1, p.2)} :=
    measurableSet_lt measurable_const (measurable_normalizedGaussianValueModulus N r)
  apply (Measure.ae_ae_comm hset).mp
  apply ae_of_all
  intro θ
  have h := complexGaussianSum_small_ball
    (fun k => normalizedRadialCoefficients N r k * (AddCircle.toCircle (radianToUnitCircle θ) : ℂ) ^ k.val)
    (by rw [sum_sq_norm_fourier_phases, sum_sq_norm_normalizedRadialCoefficients]) (u := 0) (by norm_num)
  rw [ae_iff]
  simp only [not_lt]
  apply le_antisymm _ (by positivity)
  simpa only [normalizedGaussianValueModulus, gaussianFourierPolynomial,
    mul_zero, ENNReal.ofReal_zero] using h

/-- The normalized logarithm has angular `L²` sections almost surely. -/
theorem memLp_normalizedGaussian_log (N : ℕ) (r : ℝ) :
    ∀ᵐ g ∂gaussianCoefficientMeasure (N + 1),
      MemLp (fun θ => Real.log (normalizedGaussianValueModulus N r (θ, g))) 2 radianIntervalMeasure := by
  have h := (integrable_normalizedGaussian_log_moment N r (by norm_num : (1 : ℝ) ≤ 2)).prod_right_ae
  filter_upwards [h] with g hg
  apply (memLp_two_iff_integrable_sq
    (((measurable_normalizedGaussianValueModulus N r).comp
      (measurable_id.prodMk measurable_const)).log.aestronglyMeasurable)).mpr
  simpa only [Real.rpow_two, sq_abs, Function.comp_def, id_eq] using hg

/-- The normalized angular energy is pathwise the weighted Gaussian coefficient energy. -/
theorem integral_normalizedGaussianValueModulus_sq (N : ℕ) (r : ℝ) (g : Fin (N + 1) → ℝ) :
    (∫ θ, normalizedGaussianValueModulus N r (θ, g) ^ 2 ∂radianIntervalMeasure) =
      gaussianWeightedEnergy (radialEnergyWeight N r) g := by
  have hm : AEStronglyMeasurable (fun θ =>
      ‖gaussianFourierPolynomial (normalizedRadialCoefficients N r) g θ‖ ^ 2) AddCircle.haarAddCircle := by
    unfold gaussianFourierPolynomial complexGaussianSum
    fun_prop
  have hmap := measurePreserving_radianToUnitCircle.map_eq
  have h := integral_map measurePreserving_radianToUnitCircle.measurable.aemeasurable
    (show AEStronglyMeasurable (fun θ =>
      ‖gaussianFourierPolynomial (normalizedRadialCoefficients N r) g θ‖ ^ 2)
      (Measure.map radianToUnitCircle radianIntervalMeasure) by rwa [hmap])
  rw [hmap, integral_norm_sq_gaussianFourierPolynomial] at h
  simpa only [normalizedGaussianValueModulus, norm_sq_normalizedRadialCoefficients,
    gaussianWeightedEnergy] using h.symm

/-- Squared normalized values are angularly integrable for every Gaussian coefficient vector. -/
theorem integrable_normalizedGaussianValueModulus_sq (N : ℕ) (r : ℝ) (g : Fin (N + 1) → ℝ) :
    Integrable (fun θ => normalizedGaussianValueModulus N r (θ, g) ^ 2) radianIntervalMeasure := by
  have hc : Continuous (fun θ => gaussianFourierPolynomial (normalizedRadialCoefficients N r) g θ) := by
    unfold gaussianFourierPolynomial complexGaussianSum
    fun_prop
  have hI := (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := AddCircle.haarAddCircle)
  exact (measurePreserving_radianToUnitCircle.integrable_comp (hc.norm.pow 2).aestronglyMeasurable).mpr hI

/-- The normalized logarithmic integral is the Jensen circle average minus `log σ`. -/
theorem integral_normalizedGaussian_log_eq (N : ℕ) (r : ℝ) :
    ∀ᵐ g ∂gaussianCoefficientMeasure (N + 1),
      (∫ θ, Real.log (normalizedGaussianValueModulus N r (θ, g)) ∂radianIntervalMeasure) =
        logCircleAverage (gaussianPolynomial N g) r - Real.log (radialSigma N r) := by
  filter_upwards [normalizedGaussianValueModulus_ae_pos N r, memLp_normalizedGaussian_log N r] with g hpos hlog
  have hi := hlog.integrable (by norm_num)
  have heq : (fun θ : ℝ => Real.log ‖(gaussianPolynomial N g).eval
      (r * Complex.exp (Complex.I * θ))‖) =ᵐ[radianIntervalMeasure]
      (fun θ => Real.log (normalizedGaussianValueModulus N r (θ, g)) + Real.log (radialSigma N r)) := by
    filter_upwards [hpos] with θ hθ
    have hn : ‖(gaussianPolynomial N g).eval (r * Complex.exp (Complex.I * θ))‖ ≠ 0 := by
      intro hz
      rw [normalizedGaussianValueModulus_eq, hz, zero_div] at hθ
      exact (lt_irrefl 0) hθ
    rw [normalizedGaussianValueModulus_eq, Real.log_div hn (radialSigma_pos N r).ne']
    ring
  have hsum := integral_congr_ae heq
  rw [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_radian_polynomial_log] at hsum
  linarith

/-- Exponential level occupation is the exact normalized Gaussian disk occupation. -/
theorem levelOccupation_normalizedGaussianValueModulus (N : ℕ) (r t : ℝ)
    (g : Fin (N + 1) → ℝ) :
    levelOccupation radianIntervalMeasure (normalizedGaussianValueModulus N r) (t, g) =
      GaussianOccupation.normalizedDiskOccupation N r (Real.exp t) g := by
  unfold levelOccupation GaussianOccupation.normalizedDiskOccupation occupation
  congr 1
  ext θ
  simp only [Set.mem_preimage]
  rw [GaussianOccupation.mem_normalizedValueDiskEvent]
  change normalizedGaussianValueModulus N r (θ, g) ≤ Real.exp t ↔ _
  rw [normalizedGaussianValueModulus_eq, div_le_iff₀ (radialSigma_pos N r)]

/-- The one-point angular occupation error coefficient. -/
def gaussianOccupationMeanConstant (K : ℝ) : ℝ := 10 * Real.exp (8 * K) + 1 / Real.pi

/-- The occupation variance coefficient, including all four angular exceptional sets. -/
def gaussianOccupationVarianceConstant (K : ℝ) : ℝ :=
  gaussianValuePairError K + 20 * Real.exp (8 * K) + 6 / Real.pi

/-- The Jensen logarithmic average of the actual Gaussian polynomial concentrates
with explicit clipping, moment, occupation, and energy exceptional probabilities. -/
theorem gaussian_logarithmic_integral_concentration (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (q : ℝ) (hq : 1 ≤ q) (T u b D : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hD : 0 < D) :
    gaussianCoefficientMeasure (N + 1) {g |
      u + 2 * T * (gaussianOccupationMeanConstant K / Real.sqrt N) +
        D * Real.sqrt (Real.exp (-2 * T) + gaussianOccupationMeanConstant K / Real.sqrt N + b) +
        2 * Real.exp (-2 * T) <
      |logCircleAverage (gaussianPolynomial N g) r - Real.log (radialSigma N r) - circularLogMean|} ≤
    ENNReal.ofReal (Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) +
      (gaussianOccupationVarianceConstant K / Real.sqrt N) / b ^ 2 +
      (32 * q) ^ (2 * q) / (D ^ 2) ^ q +
      4 * T ^ 2 * (gaussianOccupationVarianceConstant K / Real.sqrt N) / u ^ 2) := by
  let X := normalizedGaussianValueModulus N r
  let A := {g : Fin (N + 1) → ℝ | (∫ θ, X (θ, g) ^ 2 ∂radianIntervalMeasure) ≤ 2}
  let d := gaussianOccupationMeanConstant K / Real.sqrt N
  let v := gaussianOccupationVarianceConstant K / Real.sqrt N
  have hd : 0 ≤ d := by dsimp [d, gaussianOccupationMeanConstant]; positivity
  have hv : 0 ≤ v := by dsimp [v, gaussianOccupationVarianceConstant, gaussianValuePairError]; positivity
  have hmean (s : ℝ) : |(∫ g, levelOccupation radianIntervalMeasure X (s, g)
      ∂gaussianCoefficientMeasure (N + 1)) - circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d := by
    simp_rw [show X = normalizedGaussianValueModulus N r from rfl,
      levelOccupation_normalizedGaussianValueModulus]
    exact (GaussianOccupation.normalizedDiskOccupation_moments N hN K r hK hNK hrl hru hdegree _).1
  have hvar (s : ℝ) : variance (fun g => levelOccupation radianIntervalMeasure X (s, g))
      (gaussianCoefficientMeasure (N + 1)) ≤ v := by
    simp_rw [show X = normalizedGaussianValueModulus N r from rfl,
      levelOccupation_normalizedGaussianValueModulus]
    exact (GaussianOccupation.normalizedDiskOccupation_moments N hN K r hK hNK hrl hru hdegree _).2
  have hp : 1 ≤ 2 * q := by linarith
  have hI := integrable_normalizedGaussian_log_moment N r hp
  have hM := integral_normalizedGaussian_log_moment_le N r hp
  have hlogbound := logarithmic_integral_concentration_of_energy_event
    (gaussianCoefficientMeasure (N + 1)) radianIntervalMeasure X
    (measurable_normalizedGaussianValueModulus N r) (fun _ => norm_nonneg _)
    (normalizedGaussianValueModulus_ae_pos N r) (memLp_normalizedGaussian_log N r)
    (ae_of_all _ (integrable_normalizedGaussianValueModulus_sq N r)) A 2 (fun _ h => h)
    d v hd hv hmean hvar q hq hI.prod_right_ae hI.integral_prod_left
    ((32 * q) ^ (2 * q)) (by positivity) (by convert hM using 1; congr 1; ring)
    T u b D hT hu hb hD
  have hA : gaussianCoefficientMeasure (N + 1) Aᶜ ≤
      ENNReal.ofReal (Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K)))) := by
    have he : Aᶜ = {g : Fin (N + 1) → ℝ | 2 <
        ∫ θ : AddCircle (1 : ℝ),
          ‖(gaussianPolynomial N g).eval ((r : ℂ) * AddCircle.toCircle θ) /
            (radialSigma N r : ℂ)‖ ^ 2 ∂AddCircle.haarAddCircle} := by
      ext g
      simp only [A, X, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
        integral_normalizedGaussianValueModulus_sq, integral_normalizedGaussianPolynomial_energy]
    rw [he]
    exact gaussian_radial_energy_gt_two_le N hN K r hK hNK hrl hru
  have hbound := hlogbound.trans (add_le_add hA le_rfl)
  have hevents : {g | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
      (2 / 2 + 1) * Real.exp (-2 * T) < |∫ θ, Real.log (X (θ, g)) ∂radianIntervalMeasure - circularLogMean|}
      =ᵐ[gaussianCoefficientMeasure (N + 1)]
      {g | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
      2 * Real.exp (-2 * T) <
        |logCircleAverage (gaussianPolynomial N g) r - Real.log (radialSigma N r) - circularLogMean|} := by
    filter_upwards [integral_normalizedGaussian_log_eq N r] with g hg
    simp only [X, hg]
    norm_num
  rw [measure_congr hevents] at hbound
  refine hbound.trans_eq ?_
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
  congr 1
  ring

end Erdos522
