/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.ValuePairs
import Erdos522.Probability.Covariance.AngularExceptions
import Erdos522.Probability.OccupationMoments

/-!
# Occupation moments for normalized Rademacher polynomials

The one- and two-point circular approximations and their angular exceptional
sets control the mean and variance of the actual angular disk occupation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp Metric
open scoped RealInnerProductSpace MatrixOrder

namespace Erdos522

local instance occupationValueConvexSpace : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.ConvexSpace.ofModule
local instance occupationValueModuleConvexSpace :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- At a fixed sign vector the normalized polynomial value depends continuously on the angle. -/
theorem continuous_realRademacherValue_angle (N : ℕ) (r : ℝ) (ω : LogMoments.SignVector N) :
    Continuous (fun θ : ℝ => realRademacherValue N r (Complex.exp (Complex.I * θ)) ω) := by
  simp only [realRademacherValue, signVectorSum, realValueCoefficient]
  fun_prop

/-- The actual normalized disk event on angle and sign space. -/
def normalizedValueDiskEvent (N : ℕ) (r t : ℝ) : Set (ℝ × LogMoments.SignVector N) :=
  {p | realRademacherValue N r (Complex.exp (Complex.I * p.1)) p.2 ∈ closedBall 0 t}

/-- The finite sign model discharges joint measurability of the disk event. -/
theorem measurableSet_normalizedValueDiskEvent (N : ℕ) (r t : ℝ) :
    MeasurableSet (normalizedValueDiskEvent N r t) :=
  measurableSet_closedBall.preimage
    (measurable_from_prod_countable_left fun ω => (continuous_realRademacherValue_angle N r ω).measurable)

/-- The vector disk event is exactly the normalized polynomial modulus event. -/
theorem mem_normalizedValueDiskEvent (N : ℕ) (r t θ : ℝ) (ω : LogMoments.SignVector N) :
    (θ, ω) ∈ normalizedValueDiskEvent N r t ↔
      ‖(rademacherPolynomial N ω).eval (r * Complex.exp (Complex.I * θ))‖ ≤ t * radialSigma N r := by
  change realRademacherValue N r (Complex.exp (Complex.I * θ)) ω ∈ closedBall 0 t ↔ _
  rw [mem_closedBall, dist_zero_right, realRademacherValue_eq_polynomial]
  have hnorm (q : ℂ) : ‖(toLp 2 ![q.re / radialSigma N r, q.im / radialSigma N r] :
      EuclideanSpace ℝ (Fin 2))‖ = ‖q‖ / radialSigma N r := by
    apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (radialSigma_pos N r).le)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hnorm, div_le_iff₀ (radialSigma_pos N r)]

/-- The angular occupation uses normalized Lebesgue measure and the exact standard deviation. -/
def normalizedDiskOccupation (N : ℕ) (r t : ℝ) : LogMoments.SignVector N → ℝ :=
  occupation radianIntervalMeasure (normalizedValueDiskEvent N r t)

/-- The occupation is precisely the normalized angular measure of small polynomial values. -/
theorem normalizedDiskOccupation_eq (N : ℕ) (r t : ℝ) (ω : LogMoments.SignVector N) :
    normalizedDiskOccupation N r t ω = radianIntervalMeasure.real
      {θ : ℝ | ‖(rademacherPolynomial N ω).eval (r * Complex.exp (Complex.I * θ))‖ ≤
        t * radialSigma N r} := by
  unfold normalizedDiskOccupation occupation
  congr 1
  ext θ
  exact mem_normalizedValueDiskEvent N r t θ ω

/-- Closed disks are convex in the real vector formulation used by Bentkus. -/
theorem isConvexSet_value_closedBall (t : ℝ) :
    Convexity.IsConvexSet ℝ (closedBall (0 : EuclideanSpace ℝ (Fin 2)) t) := by
  apply Convexity.IsConvexSet.of_convexCombPair_mem
  intro a b ha hb hab x hx y hy
  simpa [Convexity.convexCombPair_eq_sum] using
    (convex_iff_add_mem.mp (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) t)) hx hy ha hb hab

/-- The disk-section probability is the event probability under the normalized value law. -/
theorem measureReal_normalizedValueDiskEvent_section (N : ℕ) (r t θ : ℝ) :
    (LogMoments.signMeasure N).real (Prod.mk θ ⁻¹' normalizedValueDiskEvent N r t) =
      ((LogMoments.signMeasure N).map
        (realRademacherValue N r (Complex.exp (Complex.I * θ)))).real (closedBall 0 t) := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (measurable_of_finite _) measurableSet_closedBall]
  rfl

/-- The mean and variance constants are uniform over the disk threshold. -/
theorem exists_normalizedDiskOccupation_moment_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (t : ℝ),
      |(∫ ω, normalizedDiskOccupation N r t ω ∂LogMoments.signMeasure N) -
        circularGaussian.real (closedBall 0 t)| ≤
          (valueGaussianErrorConstant C K + 1 / Real.pi) / Real.sqrt N ∧
      variance (normalizedDiskOccupation N r t) (LogMoments.signMeasure N) ≤
        (valuePairGaussianErrorConstant C K + 2 * valueGaussianErrorConstant C K +
          6 / Real.pi) / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_circular_gaussian_approximation_value_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_circular_gaussian_approximation_value_pair_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N hN K r hK hNK hrl hru hdegree t
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
  have hvmono : valueGaussianErrorConstant C₁ K ≤ valueGaussianErrorConstant (C₁ + C₂) K := by
    unfold valueGaussianErrorConstant
    gcongr
    linarith
  have hpmono : valuePairGaussianErrorConstant C₂ K ≤ valuePairGaussianErrorConstant (C₁ + C₂) K := by
    unfold valuePairGaussianErrorConstant valueGaussianErrorConstant jetGaussianErrorConstant pairedJetGaussianErrorConstant
    gcongr <;> linarith
  have hv0 : 0 ≤ valueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    unfold valueGaussianErrorConstant
    positivity
  have hp0 : 0 ≤ valuePairGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    unfold valuePairGaussianErrorConstant valueGaussianErrorConstant jetGaussianErrorConstant pairedJetGaussianErrorConstant
    positivity
  have hgood₁ (θ : ℝ) (hθ : θ ∉ B₁) :
      |(LogMoments.signMeasure N).real (Prod.mk θ ⁻¹' E) - p| ≤
        valueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    have hθ' : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖ := le_of_not_gt hθ
    rw [measureReal_normalizedValueDiskEvent_section]
    exact (h₁ N hN K r θ hK hNK hrl hru hdegree' hθ' (closedBall 0 t)
      measurableSet_closedBall (isConvexSet_value_closedBall t)).trans
      (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  have hgood₂ (q : ℝ × ℝ) (hq : q ∉ B₂) :
      |(LogMoments.signMeasure N).real {ω | (q.1, ω) ∈ E ∧ (q.2, ω) ∈ E} - p ^ 2| ≤
        valuePairGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    change ¬ (_ ∨ _ ∨ _ ∨ _) at hq
    simp only [not_or, not_lt] at hq
    have h := h₂ N hN K r r q.1 q.2 hK hNK hrl hru hrl hru hdegree hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
      (closedBall 0 t) (closedBall 0 t) measurableSet_closedBall measurableSet_closedBall
      (isConvexSet_value_closedBall t) (isConvexSet_value_closedBall t)
    simpa only [E, normalizedValueDiskEvent, Set.mem_ofPred_eq, p, pow_two] using
      h.trans (div_le_div_of_nonneg_right hpmono (Real.sqrt_nonneg N))
  have hm := integral_occupation_error_le (LogMoments.signMeasure N) radianIntervalMeasure hE p
    (valueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N) (1 / Real.pi / Real.sqrt N)
    measureReal_nonneg measureReal_le_one hv0 B₁ hB₁ hbad₁ hgood₁
  have hv := variance_occupation_le (LogMoments.signMeasure N) radianIntervalMeasure hE p
    (valueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N) (1 / Real.pi / Real.sqrt N)
    (valuePairGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N) (4 / Real.pi / Real.sqrt N)
    measureReal_nonneg measureReal_le_one hv0 hp0 B₁ hB₁ hbad₁ B₂ hB₂ hbad₂ hgood₁ hgood₂
  constructor
  · exact hm.trans_eq (by ring)
  · exact hv.trans_eq (by ring)

end Erdos522
