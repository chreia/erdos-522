/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianLogarithmicMoments
import Erdos522.Probability.CircularGaussianOccupation
import Erdos522.Probability.CoefficientRadialValues

/-!
# Radial logarithmic moments for CircularGaussian polynomials

Normalized radial coefficients transfer the uniform Fourier logarithmic
estimate to polynomial circle averages. The radian-to-circle map preserves
the normalized angular measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped BigOperators
namespace Erdos522

/-- Changing normalized radian angles to the unit additive circle preserves
the full coefficient-angle product law. -/
theorem measurePreserving_circularGaussian_radian_circle (N : ℕ) :
    MeasurePreserving (fun q : (Fin (N + 1) → ℂ) × ℝ => (q.1, radianToUnitCircle q.2))
      ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).prod radianIntervalMeasure)
      ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).prod AddCircle.haarAddCircle) :=
  (MeasurePreserving.id _).prod measurePreserving_radianToUnitCircle

/-- Joint logarithmic moments are integrable under the actual CircularGaussian law. -/
theorem integrable_normalizedCircularGaussian_log_moment (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun q : (Fin (N + 1) → ℂ) × ℝ =>
      |Real.log (normalizedCoefficientValueModulus N r (q.2, q.1))| ^ p)
      ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).prod radianIntervalMeasure) := by
  have hI := (circularGaussian_fourier_logarithmic_moments (normalizedRadialCoefficients N r)
    (sum_sq_norm_normalizedRadialCoefficients N r) hp).1
  have hm := ((continuous_weightedCoefficientFourier (normalizedRadialCoefficients N r)).measurable.norm.log).norm.pow_const p
  exact (measurePreserving_circularGaussian_radian_circle N).integrable_comp hm.aestronglyMeasurable |>.mpr hI

/-- The radial logarithmic moment has the coefficient-uniform first-order moment bound. -/
theorem integral_normalizedCircularGaussian_log_moment_le (N : ℕ) (r : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ a, ∫ θ, |Real.log (normalizedCoefficientValueModulus N r (θ, a))| ^ p
      ∂radianIntervalMeasure ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) ≤
        (16 * p) ^ p := by
  obtain ⟨hI, hbound⟩ := circularGaussian_fourier_logarithmic_moments (normalizedRadialCoefficients N r)
    (sum_sq_norm_normalizedRadialCoefficients N r) hp
  have hmap := (measurePreserving_circularGaussian_radian_circle N).map_eq
  have hm := ((continuous_weightedCoefficientFourier (normalizedRadialCoefficients N r)).measurable.norm.log).norm.pow_const p
  have hi := integral_map (measurePreserving_circularGaussian_radian_circle N).measurable.aemeasurable
    (show AEStronglyMeasurable (fun q => |Real.log ‖weightedCoefficientFourier
      (normalizedRadialCoefficients N r) q‖| ^ p) _ by rw [hmap]; exact hm.aestronglyMeasurable)
  rw [hmap] at hi
  rw [← integral_prod _ (integrable_normalizedCircularGaussian_log_moment N r hp)]
  rw [integral_prod _ hI] at hi
  exact hi.symm.trans_le hbound

/-- At each angle, the normalized value has circular Gaussian law and is nonzero almost surely. -/
theorem normalizedCoefficientValueModulus_circularGaussian_ae_pos (N : ℕ) (r : ℝ) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian),
      ∀ᵐ θ ∂radianIntervalMeasure, 0 < normalizedCoefficientValueModulus N r (θ, a) := by
  have hset : MeasurableSet {p : ℝ × (Fin (N + 1) → ℂ) |
      0 < normalizedCoefficientValueModulus N r (p.1, p.2)} :=
    measurableSet_lt measurable_const (measurable_normalizedCoefficientValueModulus N r)
  apply (Measure.ae_ae_comm hset).mp
  apply ae_of_all
  intro θ
  let a : Fin (N+1) → ℂ := fun k => normalizedRadialCoefficients N r k *
    fourier (k.val : ℤ) (radianToUnitCircle θ)
  have ha : ∑ k, ‖a k‖ ^ 2 = 1 := by
    simpa only [a, norm_mul, fourier_apply, Circle.norm_coe, mul_one] using
      sum_sq_norm_normalizedRadialCoefficients N r
  have hmap := map_complexCoefficientSum_circularGaussian a ha
  have h := ae_circularComplexGaussian_ne_zero
  rw [← hmap, ae_map_iff (measurable_complexCoefficientSum a).aemeasurable
    (show MeasurableSet {z : ℂ | z ≠ 0} by measurability)] at h
  filter_upwards [h] with ω hω
  rw [normalizedCoefficientValueModulus, weightedCoefficientFourier_eq_complexCoefficientSum,
    norm_pos_iff]
  exact hω

/-- The normalized logarithm has angular `L²` sections almost surely. -/
theorem memLp_normalizedCircularGaussian_log (N : ℕ) (r : ℝ) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian),
      MemLp (fun θ => Real.log (normalizedCoefficientValueModulus N r (θ, a))) 2 radianIntervalMeasure := by
  have h := (integrable_normalizedCircularGaussian_log_moment N r (by norm_num : (1 : ℝ) ≤ 2)).prod_right_ae
  filter_upwards [h] with a ha
  apply (memLp_two_iff_integrable_sq
    (((measurable_normalizedCoefficientValueModulus N r).comp
      (measurable_id.prodMk measurable_const)).log.aestronglyMeasurable)).mpr
  simpa only [Real.rpow_two, sq_abs, Function.comp_def, id_eq] using ha

/-- The normalized logarithmic integral equals the Jensen circle average
minus the logarithm of the exact standard deviation. -/
theorem integral_normalizedCircularGaussian_log_eq (N : ℕ) (r : ℝ) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian),
      (∫ θ, Real.log (normalizedCoefficientValueModulus N r (θ, a)) ∂radianIntervalMeasure) =
        logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r) := by
  filter_upwards [normalizedCoefficientValueModulus_circularGaussian_ae_pos N r, memLp_normalizedCircularGaussian_log N r] with a hpos hlog
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
theorem levelOccupation_normalizedCoefficientValueModulus_circularGaussian (N : ℕ) (r t : ℝ)
    (a : Fin (N + 1) → ℂ) :
    levelOccupation radianIntervalMeasure (normalizedCoefficientValueModulus N r) (t, a) =
      CircularGaussianOccupation.normalizedDiskOccupation N r (Real.exp t) a := by
  unfold levelOccupation CircularGaussianOccupation.normalizedDiskOccupation occupation
  congr 1
  ext θ
  simp only [Set.mem_preimage]
  rw [CircularGaussianOccupation.mem_normalizedValueDiskEvent]
  change normalizedCoefficientValueModulus N r (θ, a) ≤ Real.exp t ↔ _
  rw [normalizedCoefficientValueModulus_eq, div_le_iff₀ (radialSigma_pos N r)]

end Erdos522
