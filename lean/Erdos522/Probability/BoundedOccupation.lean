/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.BoundedValues
import Erdos522.Probability.GaussianApproximation.BoundedValuePairs
import Erdos522.Probability.SteinhausRadialLogMoments

/-!
# Angular occupation for bounded complex coefficients

One-point and separated two-point Gaussian comparisons control angular
occupation under the original coefficient law. The four angular exceptional
sets contribute their normalized Lebesgue measures to the variance budget.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp Metric
open scoped RealInnerProductSpace MatrixOrder
namespace Erdos522

/-- A coefficient disk section is the corresponding normalized-value law event. -/
theorem measureReal_coefficient_disk_section (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (N : ℕ) (r t θ : ℝ) :
    (Measure.pi (fun _ : Fin (N + 1) => μ)).real
      (Prod.mk θ ⁻¹' SteinhausOccupation.normalizedValueDiskEvent N r t) =
      ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
        (circularValue N r (Complex.exp (Complex.I * θ)))).real (closedBall 0 t) := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (measurable_circularValue N r _) measurableSet_closedBall]
  rfl

/-- The mean and variance constants are uniform over the disk threshold. -/
theorem exists_bounded_coefficient_occupation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (B : ℝ) (_ : 0 ≤ B) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
      (_ : (∫ z, z ∂μ) = 0) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (t : ℝ),
      |(∫ ω, levelOccupation radianIntervalMeasure (normalizedCoefficientValueModulus N r) (t, ω) ∂Measure.pi (fun _ : Fin (N + 1) => μ)) -
        circularGaussian.real (closedBall 0 (Real.exp t))| ≤
          (boundedValueGaussianErrorConstant C B K + 1 / Real.pi) / Real.sqrt N ∧
      variance (fun a => levelOccupation radianIntervalMeasure (normalizedCoefficientValueModulus N r) (t, a)) (Measure.pi (fun _ : Fin (N + 1) => μ)) ≤
        (boundedValuePairGaussianErrorConstant C B K + 2 * boundedValueGaussianErrorConstant C B K +
          6 / Real.pi) / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_gaussian_approximation_bounded_value_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_gaussian_approximation_bounded_value_pair_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro μ _ B hB hbound hmean hsecond N hN K r hK hNK hrl hru hdegree t
  simp_rw [levelOccupation_normalizedCoefficientValueModulus_steinhaus]
  let E := SteinhausOccupation.normalizedValueDiskEvent N r (Real.exp t)
  let p := circularGaussian.real (closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.exp t))
  let B₁ : Set ℝ := {θ | ‖((2 * θ : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N}
  let B₂ : Set (ℝ × ℝ) := {q | ‖((2 * q.1 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N ∨
    ‖((2 * q.2 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N ∨
    ‖((q.1 - q.2 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N ∨
    ‖((q.1 + q.2 : ℝ) : Real.Angle)‖ < 1 / Real.sqrt N}
  have hE : MeasurableSet E := SteinhausOccupation.measurableSet_normalizedValueDiskEvent N r (Real.exp t)
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
  have hvmono : boundedValueGaussianErrorConstant C₁ B K ≤ boundedValueGaussianErrorConstant (C₁ + C₂) B K := by
    unfold boundedValueGaussianErrorConstant
    gcongr
    linarith
  have hpmono : boundedValuePairGaussianErrorConstant C₂ B K ≤ boundedValuePairGaussianErrorConstant (C₁ + C₂) B K := by
    unfold boundedValuePairGaussianErrorConstant boundedValueGaussianErrorConstant boundedJetGaussianErrorConstant boundedPairedJetGaussianErrorConstant
    gcongr <;> linarith
  have hv0 : 0 ≤ boundedValueGaussianErrorConstant (C₁ + C₂) B K / Real.sqrt N := by
    unfold boundedValueGaussianErrorConstant
    positivity
  have hp0 : 0 ≤ boundedValuePairGaussianErrorConstant (C₁ + C₂) B K / Real.sqrt N := by
    unfold boundedValuePairGaussianErrorConstant boundedValueGaussianErrorConstant boundedJetGaussianErrorConstant boundedPairedJetGaussianErrorConstant
    positivity
  have hgood₁ (θ : ℝ) (hθ : θ ∉ B₁) :
      |(Measure.pi (fun _ : Fin (N + 1) => μ)).real (Prod.mk θ ⁻¹' E) - p| ≤
        boundedValueGaussianErrorConstant (C₁ + C₂) B K / Real.sqrt N := by
    have hθ' : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖ := le_of_not_gt hθ
    rw [measureReal_coefficient_disk_section]
    exact (h₁ μ B hB hbound hmean hsecond N hN K r θ hK hNK hrl hru hdegree' hθ' (closedBall 0 (Real.exp t))
      measurableSet_closedBall (isConvexSet_value_closedBall (Real.exp t))).trans
      (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  have hgood₂ (q : ℝ × ℝ) (hq : q ∉ B₂) :
      |(Measure.pi (fun _ : Fin (N + 1) => μ)).real {ω | (q.1, ω) ∈ E ∧ (q.2, ω) ∈ E} - p ^ 2| ≤
        boundedValuePairGaussianErrorConstant (C₁ + C₂) B K / Real.sqrt N := by
    change ¬ (_ ∨ _ ∨ _ ∨ _) at hq
    simp only [not_or, not_lt] at hq
    have h := h₂ μ B hB hbound hmean hsecond N hN K r r q.1 q.2 hK hNK hrl hru hrl hru hdegree hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
      (closedBall 0 (Real.exp t)) (closedBall 0 (Real.exp t)) measurableSet_closedBall measurableSet_closedBall
      (isConvexSet_value_closedBall (Real.exp t)) (isConvexSet_value_closedBall (Real.exp t))
    simpa only [E, SteinhausOccupation.normalizedValueDiskEvent, Set.mem_ofPred_eq, p, pow_two] using
      h.trans (div_le_div_of_nonneg_right hpmono (Real.sqrt_nonneg N))
  have hm := integral_occupation_error_le (Measure.pi (fun _ : Fin (N + 1) => μ)) radianIntervalMeasure hE p
    (boundedValueGaussianErrorConstant (C₁ + C₂) B K / Real.sqrt N) (1 / Real.pi / Real.sqrt N)
    measureReal_nonneg measureReal_le_one hv0 B₁ hB₁ hbad₁ hgood₁
  have hv := variance_occupation_le (Measure.pi (fun _ : Fin (N + 1) => μ)) radianIntervalMeasure hE p
    (boundedValueGaussianErrorConstant (C₁ + C₂) B K / Real.sqrt N) (1 / Real.pi / Real.sqrt N)
    (boundedValuePairGaussianErrorConstant (C₁ + C₂) B K / Real.sqrt N) (4 / Real.pi / Real.sqrt N)
    measureReal_nonneg measureReal_le_one hv0 hp0 B₁ hB₁ hbad₁ B₂ hB₂ hbad₂ hgood₁ hgood₂
  constructor
  · exact hm.trans_eq (by ring)
  · exact hv.trans_eq (by ring)

end Erdos522
