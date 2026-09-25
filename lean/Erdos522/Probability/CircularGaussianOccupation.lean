/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianValues
import Erdos522.Probability.Covariance.AngularExceptions
import Erdos522.Probability.OccupationMoments

/-!
# Occupation moments for normalized Gaussian polynomials

The one- and two-point circular approximations and their angular exceptional
sets control the mean and variance of the actual angular disk occupation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp Metric
open scoped RealInnerProductSpace MatrixOrder

namespace Erdos522
namespace CircularGaussianOccupation

local instance occupationValueConvexSpace : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.ConvexSpace.ofModule
local instance occupationValueModuleConvexSpace :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- At a fixed coefficient vector the normalized polynomial value depends continuously on the angle. -/
theorem continuous_circularValue_angle (N : ℕ) (r : ℝ) (ω : Fin (N + 1) → ℂ) :
    Continuous (fun θ : ℝ => circularValue N r (Complex.exp (Complex.I * θ)) ω) := by
  simp only [circularValue, circularVectorSum, circularVector, realValueCoefficient, imaginaryValueCoefficient]
  fun_prop

/-- The actual normalized disk event on angle and Gaussian coefficient space. -/
def normalizedValueDiskEvent (N : ℕ) (r t : ℝ) : Set (ℝ × (Fin (N + 1) → ℂ)) :=
  {p | circularValue N r (Complex.exp (Complex.I * p.1)) p.2 ∈ closedBall 0 t}

/-- The finite Gaussian model discharges joint measurability of the disk event. -/
theorem measurableSet_normalizedValueDiskEvent (N : ℕ) (r t : ℝ) :
    MeasurableSet (normalizedValueDiskEvent N r t) := by
  apply measurableSet_closedBall.preimage
  simp only [circularValue, circularVectorSum, circularVector, realValueCoefficient, imaginaryValueCoefficient]
  fun_prop

/-- The vector disk event is exactly the normalized polynomial modulus event. -/
theorem mem_normalizedValueDiskEvent (N : ℕ) (r t θ : ℝ) (ω : Fin (N + 1) → ℂ) :
    (θ, ω) ∈ normalizedValueDiskEvent N r t ↔
      ‖(Polynomial.ofFn (N+1) ω).eval (r * Complex.exp (Complex.I * θ))‖ ≤ t * radialSigma N r := by
  change circularValue N r (Complex.exp (Complex.I * θ)) ω ∈ closedBall 0 t ↔ _
  rw [mem_closedBall, dist_zero_right, circularValue_eq_polynomial]
  have hnorm (q : ℂ) : ‖(toLp 2 ![q.re / radialSigma N r, q.im / radialSigma N r] :
      EuclideanSpace ℝ (Fin 2))‖ = ‖q‖ / radialSigma N r := by
    apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (radialSigma_pos N r).le)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hnorm, div_le_iff₀ (radialSigma_pos N r)]

/-- The angular occupation uses normalized Lebesgue measure and the exact standard deviation. -/
def normalizedDiskOccupation (N : ℕ) (r t : ℝ) : (Fin (N + 1) → ℂ) → ℝ :=
  occupation radianIntervalMeasure (normalizedValueDiskEvent N r t)

/-- The occupation is precisely the normalized angular measure of small polynomial values. -/
theorem normalizedDiskOccupation_eq (N : ℕ) (r t : ℝ) (ω : Fin (N + 1) → ℂ) :
    normalizedDiskOccupation N r t ω = radianIntervalMeasure.real
      {θ : ℝ | ‖(Polynomial.ofFn (N+1) ω).eval (r * Complex.exp (Complex.I * θ))‖ ≤
        t * radialSigma N r} := by
  unfold normalizedDiskOccupation occupation
  congr 1
  ext θ
  exact mem_normalizedValueDiskEvent N r t θ ω

/-- The disk-section probability is the event probability under the normalized value law. -/
theorem measureReal_normalizedValueDiskEvent_section (N : ℕ) (r t θ : ℝ) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (Prod.mk θ ⁻¹' normalizedValueDiskEvent N r t) =
      ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).map
        (circularValue N r (Complex.exp (Complex.I * θ)))).real (closedBall 0 t) := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (measurable_circularValue N r _) measurableSet_closedBall]
  rfl

/-- The mean and variance constants are uniform over the disk threshold. -/
theorem normalizedDiskOccupation_moments (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (t : ℝ) :
    |(∫ g, normalizedDiskOccupation N r t g ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) -
      circularGaussian.real (closedBall 0 t)| ≤
        (10 * Real.exp (8 * K) + 1 / Real.pi) / Real.sqrt N ∧
    variance (normalizedDiskOccupation N r t) (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) ≤
      (circularGaussianValuePairError K + 20 * Real.exp (8 * K) + 6 / Real.pi) / Real.sqrt N := by
  let E := normalizedValueDiskEvent N r t
  let p := circularGaussian.real (closedBall (0 : EuclideanSpace ℝ (Fin 2)) t)
  let B₁ : Set ℝ := {θ | ‖((2 * θ : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N}
  let B₂ : Set (ℝ × ℝ) := {q | ‖((2 * q.1 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N ∨
    ‖((2 * q.2 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N ∨
    ‖((q.1 - q.2 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N ∨
    ‖((q.1 + q.2 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N}
  have hE : MeasurableSet E := measurableSet_normalizedValueDiskEvent N r t
  have hB₁ : MeasurableSet B₁ := measurableSet_lt
    (show Continuous (fun θ : ℝ => ‖((2 * θ : ℝ) : Real.Angle)‖) by fun_prop).measurable measurable_const
  have hB₂ : MeasurableSet B₂ := by
    apply MeasurableSet.union
    · exact measurableSet_lt
        (show Continuous (fun q : ℝ × ℝ => ‖((2 * q.1 : ℝ) : Real.Angle)‖) by fun_prop).measurable measurable_const
    · apply MeasurableSet.union
      · exact measurableSet_lt
          (show Continuous (fun q : ℝ × ℝ => ‖((2 * q.2 : ℝ) : Real.Angle)‖) by fun_prop).measurable measurable_const
      · exact (measurableSet_lt
          (show Continuous (fun q : ℝ × ℝ => ‖((q.1 - q.2 : ℝ) : Real.Angle)‖) by fun_prop).measurable measurable_const).union
          (measurableSet_lt
          (show Continuous (fun q : ℝ × ℝ => ‖((q.1 + q.2 : ℝ) : Real.Angle)‖) by fun_prop).measurable measurable_const)
  have hbad₁ : radianIntervalMeasure.real B₁ ≤ 1 / Real.pi / Real.sqrt N := by
    simpa only [B₁, div_right_comm] using radianInterval_angularResonance_le
      (1 / Real.sqrt N) (by positivity)
  have hbad₂ : (radianIntervalMeasure.prod radianIntervalMeasure).real B₂ ≤ 4 / Real.pi / Real.sqrt N := by
    have h := radianInterval_angularPairExceptions_le (1 / Real.sqrt N) (by positivity)
    convert h using 1
    ring
  have hdegree' : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ (6400 * Real.exp (8 * K)) ^ 2 := by gcongr; norm_num
      _ ≤ _ := hdegree
  have hv0 : 0 ≤ (10 * Real.exp (8 * K)) / Real.sqrt N := by positivity
  have hp0 : 0 ≤ circularGaussianValuePairError K / Real.sqrt N := by
    unfold circularGaussianValuePairError
    positivity
  have hgood₁ (θ : ℝ) (hθ : θ ∉ B₁) :
      |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (Prod.mk θ ⁻¹' E) - p| ≤
        (10 * Real.exp (8 * K)) / Real.sqrt N := by
    have hθ' : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖ := le_of_not_gt hθ
    exact circularGaussian_value_circular_comparison N hN K r θ hK hNK hrl hru hdegree' hθ' (closedBall 0 t)
      measurableSet_closedBall
  have hgood₂ (q : ℝ × ℝ) (hq : q ∉ B₂) :
      |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {ω | (q.1, ω) ∈ E ∧ (q.2, ω) ∈ E} - p ^ 2| ≤
        circularGaussianValuePairError K / Real.sqrt N := by
    change ¬ (_ ∨ _ ∨ _ ∨ _) at hq
    simp only [not_or, not_lt] at hq
    have h := circularGaussian_value_pair_circular_comparison N hN K r r q.1 q.2 hK hNK hrl hru hrl hru
      hdegree hq.1 hq.2.1 hq.2.2.1 hq.2.2.2 (closedBall 0 t) (closedBall 0 t)
      measurableSet_closedBall measurableSet_closedBall
    simpa only [E, normalizedValueDiskEvent, Set.mem_ofPred_eq, p, pow_two] using h
  have hm := integral_occupation_error_le (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) radianIntervalMeasure hE p
    ((10 * Real.exp (8 * K)) / Real.sqrt N) (1 / Real.pi / Real.sqrt N)
    measureReal_nonneg measureReal_le_one hv0 B₁ hB₁ hbad₁ hgood₁
  have hv := variance_occupation_le (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) radianIntervalMeasure hE p
    ((10 * Real.exp (8 * K)) / Real.sqrt N) (1 / Real.pi / Real.sqrt N)
    (circularGaussianValuePairError K / Real.sqrt N) (4 / Real.pi / Real.sqrt N)
    measureReal_nonneg measureReal_le_one hv0 hp0 B₁ hB₁ hbad₁ B₂ hB₂ hbad₂ hgood₁ hgood₂
  constructor
  · exact hm.trans_eq (by ring)
  · exact hv.trans_eq (by ring)

end CircularGaussianOccupation
end Erdos522
