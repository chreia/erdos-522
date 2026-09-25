/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausVectorMoments
import Erdos522.Probability.BoundedComplexHoeffding

/-!
# Covariance of real vectors with complex coefficients

A complex coefficient acts through its real and imaginary parts. For any
centered coefficient law with a finite second moment, independence expresses
the covariance of a sum as the integral of its deterministic Gram form.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal
namespace Erdos522

/-- The real linear map specified by the images of the complex basis `1, I`. -/
def complexCoefficientLinearMap {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    ℂ →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  Complex.reCLM.smulRight a + Complex.imCLM.smulRight b

theorem complexCoefficientLinearMap_apply {d : ℕ}
    (a b : EuclideanSpace ℝ (Fin d)) (z : ℂ) :
    complexCoefficientLinearMap a b z = circularVector a b z := rfl

/-- A finite coefficient moment is preserved by each real linear image. -/
theorem memLp_complexCoefficientVector (μ : Measure ℂ) {p : ℝ≥0∞}
    (hp : MemLp (fun z : ℂ => z) p μ) {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    MemLp (circularVector a b) p μ :=
  hp.continuousLinearMap_comp (complexCoefficientLinearMap a b)

theorem integral_complexCoefficientVector_eq_zero (μ : Measure ℂ)
    (hI : Integrable (fun z : ℂ => z) μ) (hmean : (∫ z, z ∂μ) = 0)
    {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    (∫ z, circularVector a b z ∂μ) = 0 := by
  change (∫ z, complexCoefficientLinearMap a b z ∂μ) = 0
  rw [(complexCoefficientLinearMap a b).integral_comp_comm hI, hmean, map_zero]

/-- A centered coefficient vector has covariance equal to its second product moment. -/
theorem covarianceBilin_complexCoefficientVector (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    {d : ℕ} (a b x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin (μ.map (circularVector a b)) x y =
      ∫ z, ⟪x, circularVector a b z⟫ * ⟪y, circularVector a b z⟫ ∂μ := by
  have hv := memLp_complexCoefficientVector μ h2 a b
  rw [covarianceBilin_map_apply_eq_cov_projection hv,
    covariance_eq_sub (hv.const_inner x) (hv.const_inner y)]
  have hm (v : EuclideanSpace ℝ (Fin d)) : (∫ z, ⟪v, circularVector a b z⟫ ∂μ) = 0 := by
    rw [integral_inner (hv.integrable (by norm_num)),
      integral_complexCoefficientVector_eq_zero μ (h2.integrable (by norm_num)) hmean]
    simp
  rw [hm x, hm y, mul_zero, sub_zero]
  rfl

/-- Independent complex coefficients add their covariance forms. -/
theorem covarianceBilin_complexCoefficientSum (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    {n d : ℕ} (a b : Fin n → EuclideanSpace ℝ (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin ((Measure.pi (fun _ : Fin n => μ)).map (circularVectorSum a b)) x y =
      ∫ z, ∑ k, ⟪x, circularVector (a k) (b k) z⟫ *
        ⟪y, circularVector (a k) (b k) z⟫ ∂μ := by
  have hv (k : Fin n) := memLp_complexCoefficientVector μ h2 (a k) (b k)
  have hcoord (k : Fin n) :
      MemLp (fun ω : Fin n → ℂ => circularVector (a k) (b k) (ω k)) 2
        (Measure.pi (fun _ => μ)) :=
    (hv k).comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) k)
  have hind : iIndepFun (fun k (ω : Fin n → ℂ) => circularVector (a k) (b k) (ω k))
      (Measure.pi (fun _ => μ)) :=
    iIndepFun_pi (fun k => (show Measurable (circularVector (a k) (b k)) by
      unfold circularVector; fun_prop).aemeasurable)
  unfold circularVectorSum
  rw [covarianceBilin_map_sum_eq_sum hcoord hind,
    integral_finsetSum _ (fun k _ => (hv k).const_inner x |>.integrable_mul ((hv k).const_inner y))]
  apply Finset.sum_congr rfl
  intro k _
  have hm := measurePreserving_eval (fun _ : Fin n => μ) k
  have hmap : (Measure.pi (fun _ : Fin n => μ)).map
      (fun ω => circularVector (a k) (b k) (ω k)) = μ.map (circularVector (a k) (b k)) := by
    change (Measure.pi (fun _ : Fin n => μ)).map
      ((circularVector (a k) (b k)) ∘ Function.eval k) = _
    rw [← Measure.map_map (by unfold circularVector; fun_prop) hm.measurable, hm.map_eq]
  rw [hmap, covarianceBilin_complexCoefficientVector μ h2 hmean]

/-- A deterministic Gram lower bound, integrated against a unit-second-moment
coefficient law, gives the same covariance lower bound. -/
theorem covarianceBilin_complexCoefficientSum_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    {n d : ℕ} (a b : Fin n → EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hgram : ∀ z : ℂ, ∀ x : EuclideanSpace ℝ (Fin d),
      c * (‖z‖ ^ 2 * ‖x‖ ^ 2) ≤ ∑ k, ⟪x, circularVector (a k) (b k) z⟫ ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    c * ‖x‖ ^ 2 ≤ covarianceBilin
      ((Measure.pi (fun _ : Fin n => μ)).map (circularVectorSum a b)) x x := by
  rw [covarianceBilin_complexCoefficientSum μ h2 hmean]
  have hI : Integrable (fun z => ∑ k, ⟪x, circularVector (a k) (b k) z⟫ ^ 2) μ :=
    integrable_finsetSum _ (fun k _ =>
      ((memLp_complexCoefficientVector μ h2 (a k) (b k)).const_inner x).integrable_sq)
  calc
    _ = ∫ z, c * (‖z‖ ^ 2 * ‖x‖ ^ 2) ∂μ := by
      rw [integral_const_mul, integral_mul_const, hnorm, one_mul]
    _ ≤ ∫ z, ∑ k, ⟪x, circularVector (a k) (b k) z⟫ ^ 2 ∂μ :=
      integral_mono ((h2.norm.integrable_sq.mul_const _).const_mul _) hI (fun z => hgram z x)
    _ = _ := by simp only [pow_two]

end Erdos522
