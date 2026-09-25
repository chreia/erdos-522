/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianRadialLogMoments

/-!
# Exact laws of normalized circular Gaussian values

Every normalized polynomial value is standard circular Gaussian, at every
radius and angle. Consequently both its disk occupation mean and its
logarithmic expectation are exact finite-degree identities.
-/

noncomputable section
open MeasureTheory ProbabilityTheory WithLp Set Metric
open scoped BigOperators
namespace Erdos522

/-- Finite polynomial evaluation is measurable in its coefficient vector. -/
@[fun_prop]
theorem measurable_normalizedCoefficientPolynomial (N : ℕ) (r : ℝ) (z : ℂ) :
    Measurable (fun a : Fin (N+1) → ℂ =>
      (Polynomial.ofFn (N+1) a).eval ((r : ℂ) * z) / (radialSigma N r : ℂ)) := by
  simp only [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  fun_prop

/-- Exactly normalized values are circular Gaussian at every radius and point of the unit circle. -/
theorem map_normalizedCircularGaussianPolynomial (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).map
      (fun a => (Polynomial.ofFn (N + 1) a).eval ((r : ℂ) * z) / (radialSigma N r : ℂ)) =
      circularComplexGaussian := by
  let c : Fin (N + 1) → ℂ := fun k => normalizedRadialCoefficients N r k * z ^ k.val
  have hc : ∑ k, ‖c k‖ ^ 2 = 1 := by
    simpa only [c, norm_mul, norm_pow, hz, one_pow, mul_one] using
      sum_sq_norm_normalizedRadialCoefficients N r
  have he : (fun a => (Polynomial.ofFn (N + 1) a).eval ((r : ℂ) * z) /
      (radialSigma N r : ℂ)) = complexCoefficientSum c := by
    funext a
    rw [Polynomial.ofFn_eq_sum_monomial]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.sum_div,
      complexCoefficientSum, c, normalizedRadialCoefficients, mul_pow]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  exact map_complexCoefficientSum_circularGaussian c hc

/-- Real coordinates are inverse to the complex identification of the Euclidean plane. -/
theorem complex_coordinates_valueComplexLinearMap (x : EuclideanSpace ℝ (Fin 2)) :
    (toLp 2 ![(valueComplexLinearMap x).re, (valueComplexLinearMap x).im] :
      EuclideanSpace ℝ (Fin 2)) = x := by
  ext i
  fin_cases i <;> simp

/-- The exact normalized real two-vector has the standard circular Gaussian law. -/
theorem map_circularGaussianValue (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).map
      (circularValue N r z) = circularGaussian := by
  let f : ℂ → EuclideanSpace ℝ (Fin 2) := fun w => toLp 2 ![w.re, w.im]
  have hf : Measurable f := by unfold f; fun_prop
  have h := congrArg (Measure.map f) (map_normalizedCircularGaussianPolynomial N r z hz)
  rw [Measure.map_map hf (by fun_prop), circularComplexGaussian,
    Measure.map_map hf valueComplexLinearMap.measurable] at h
  have he : f ∘ valueComplexLinearMap = id := by
    funext x
    exact complex_coordinates_valueComplexLinearMap x
  rw [he, Measure.map_id] at h
  convert h using 1
  congr 1
  funext a
  rw [circularValue_eq_polynomial]
  simp only [Function.comp_apply, f, Complex.div_ofReal_re, Complex.div_ofReal_im]

/-- The angular occupation mean is the circular disk distribution at every finite degree. -/
theorem integral_circularGaussianDiskOccupation (N : ℕ) (r t : ℝ) :
    (∫ a, CircularGaussianOccupation.normalizedDiskOccupation N r t a
      ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) =
        circularGaussian.real (closedBall 0 t) := by
  rw [CircularGaussianOccupation.normalizedDiskOccupation,
    integral_occupation _ _ (CircularGaussianOccupation.measurableSet_normalizedValueDiskEvent N r t)]
  have hsection (θ : ℝ) :
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
        (Prod.mk θ ⁻¹' CircularGaussianOccupation.normalizedValueDiskEvent N r t) =
          circularGaussian.real (closedBall 0 t) := by
    rw [CircularGaussianOccupation.measureReal_normalizedValueDiskEvent_section,
      map_circularGaussianValue N r _ (Complex.norm_exp_I_mul_ofReal θ)]
  simp_rw [hsection]
  simp

/-- A normalized logarithmic value has the same expectation at every radius and angle. -/
theorem integral_log_normalizedCircularGaussian_value (N : ℕ) (r θ : ℝ) :
    (∫ a, Real.log (normalizedCoefficientValueModulus N r (θ, a))
      ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) = circularLogMean := by
  have hmap := map_normalizedCircularGaussianPolynomial N r
    (Complex.exp (Complex.I * θ)) (Complex.norm_exp_I_mul_ofReal θ)
  have h := congrArg (fun μ : Measure ℂ => ∫ z, Real.log ‖z‖ ∂μ) hmap
  have hm : Measurable (fun z : ℂ => Real.log ‖z‖) := measurable_norm.log
  rw [integral_map (measurable_normalizedCoefficientPolynomial N r _).aemeasurable
    hm.aestronglyMeasurable, circularComplexGaussian,
    integral_map valueComplexLinearMap.measurable.aemeasurable hm.aestronglyMeasurable] at h
  simp only [norm_valueComplexLinearMap] at h
  change _ = ∫ x, Real.log ‖x‖ ∂circularGaussian
  convert h using 1
  apply integral_congr_ae
  filter_upwards with a
  rw [normalizedCoefficientValueModulus_eq, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (radialSigma_pos N r)]

/-- The Jensen logarithmic average has the exact finite-degree Gaussian mean. -/
theorem integral_circularGaussian_logCircleAverage_centered (N : ℕ) (r : ℝ) :
    (∫ a, logCircleAverage (Polynomial.ofFn (N + 1) a) r - Real.log (radialSigma N r)
      ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) = circularLogMean := by
  have hnorm := integrable_normalizedCircularGaussian_log_moment N r (by norm_num : (1 : ℝ) ≤ 1)
  have hm : AEStronglyMeasurable (fun q : (Fin (N+1) → ℂ) × ℝ =>
      Real.log (normalizedCoefficientValueModulus N r (q.2, q.1)))
      ((Measure.pi (fun _ : Fin (N+1) => circularComplexGaussian)).prod radianIntervalMeasure) := by
    exact (((measurable_normalizedCoefficientValueModulus N r).comp measurable_swap).log).aestronglyMeasurable
  have hI := (integrable_norm_iff hm).mp (by
    simpa only [Real.rpow_one, Real.norm_eq_abs] using hnorm)
  rw [← integral_congr_ae (integral_normalizedCircularGaussian_log_eq N r),
    integral_integral_swap hI]
  simp_rw [integral_log_normalizedCircularGaussian_value]
  simp

end Erdos522
