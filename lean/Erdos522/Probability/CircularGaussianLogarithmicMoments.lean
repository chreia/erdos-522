/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianSums
import Erdos522.Probability.CircularGaussianRepresentation
import Erdos522.Probability.GaussianLogarithmicMoments
import Erdos522.Probability.CoefficientRadialValues

/-!
# Uniform logarithmic moments for circular Gaussian Fourier sums

Every normalized complex linear combination has the same circular Gaussian
law. Its logarithmic moments therefore have the uniform bound `(16 p)^p`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Erdos522

/-- The circular Gaussian has quantitative logarithmic moments of order one. -/
theorem circularComplexGaussian_logarithmic_moments {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z : ℂ => |Real.log ‖z‖| ^ p) circularComplexGaussian ∧
      (∫ z, |Real.log ‖z‖| ^ p ∂circularComplexGaussian) ≤ (16 * p) ^ p := by
  let a : Fin 2 → ℂ := ![1 / (Real.sqrt 2 : ℂ), Complex.I / (Real.sqrt 2 : ℂ)]
  have ha : ∑ k, ‖a k‖ ^ 2 = 1 := by
    simp only [a, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      norm_div, norm_one, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hm : Measurable (fun z : ℂ => |Real.log ‖z‖| ^ p) := by fun_prop
  have hg := gaussian_logarithmic_moments a ha hp
  have hmap := map_complexGaussianSum_circular
  have hI : Integrable (fun z : ℂ => |Real.log ‖z‖| ^ p) circularComplexGaussian := by
    rw [← hmap]
    exact (integrable_map_measure hm.aestronglyMeasurable
      (measurable_complexGaussianSum a).aemeasurable).mpr hg.1
  refine ⟨hI, ?_⟩
  rw [← hmap, integral_map (measurable_complexGaussianSum a).aemeasurable hm.aestronglyMeasurable]
  exact hg.2

/-- The estimate is independent of the number and shape of normalized complex coefficients. -/
theorem circularGaussian_logarithmic_moments {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun ω => |Real.log ‖complexCoefficientSum a ω‖| ^ p)
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) ∧
    (∫ ω, |Real.log ‖complexCoefficientSum a ω‖| ^ p
      ∂Measure.pi (fun _ : Fin n => circularComplexGaussian)) ≤ (16 * p) ^ p := by
  obtain ⟨hI, hbound⟩ := circularComplexGaussian_logarithmic_moments hp
  have hm : Measurable (fun z : ℂ => |Real.log ‖z‖| ^ p) := by fun_prop
  have hmap := map_complexCoefficientSum_circularGaussian a ha
  rw [← hmap] at hI hbound
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable
    (measurable_complexCoefficientSum a).aemeasurable).mp hI, ?_⟩
  rw [integral_map (measurable_complexCoefficientSum a).aemeasurable hm.aestronglyMeasurable] at hbound
  exact hbound

/-- Fourier phases express the weighted Fourier polynomial as a complex coefficient sum. -/
theorem weightedCoefficientFourier_eq_complexCoefficientSum {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ω : Fin (N + 1) → ℂ) (θ : AddCircle (1 : ℝ)) :
    weightedCoefficientFourier a (ω, θ) =
      complexCoefficientSum (fun k => a k * (fourier (k.val : ℤ) θ)) ω := by
  simp only [weightedCoefficientFourier, complexCoefficientSum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Joint coefficient-angle integrability of every absolute logarithmic moment. -/
theorem circularGaussian_fourier_logarithmic_moments {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun q : (Fin (N + 1) → ℂ) × AddCircle (1 : ℝ) =>
      |Real.log ‖weightedCoefficientFourier a q‖| ^ p)
      ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).prod AddCircle.haarAddCircle) ∧
    (∫ ω, ∫ θ, |Real.log ‖weightedCoefficientFourier a (ω, θ)‖| ^ p
      ∂AddCircle.haarAddCircle ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) ≤ (16 * p) ^ p := by
  have hm := ((continuous_weightedCoefficientFourier a).measurable.norm.log).norm.pow_const p
  have hsection (θ : AddCircle (1 : ℝ)) :
      Integrable (fun ω => |Real.log ‖weightedCoefficientFourier a (ω, θ)‖| ^ p)
        (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) ∧
      (∫ ω, |Real.log ‖weightedCoefficientFourier a (ω, θ)‖| ^ p
        ∂Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) ≤ (16 * p) ^ p := by
    simp only [weightedCoefficientFourier_eq_complexCoefficientSum]
    apply circularGaussian_logarithmic_moments _ _ hp
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using ha
  have hI : Integrable (fun q : (Fin (N + 1) → ℂ) × AddCircle (1 : ℝ) =>
      |Real.log ‖weightedCoefficientFourier a q‖| ^ p)
      ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).prod AddCircle.haarAddCircle) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ fun θ => (hsection θ).1, ?_⟩
    apply (integrable_const ((16 * p) ^ p)).mono'
    · exact hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    · filter_upwards with θ
      have hn (ω : Fin (N + 1) → ℂ) : 0 ≤ |Real.log ‖weightedCoefficientFourier a (ω, θ)‖| ^ p :=
        Real.rpow_nonneg (abs_nonneg _) _
      simp only [Real.norm_eq_abs]
      simp_rw [abs_of_nonneg (hn _)]
      rw [abs_of_nonneg (integral_nonneg_of_ae (ae_of_all _ hn))]
      exact (hsection θ).2
  refine ⟨hI, ?_⟩
  rw [integral_integral_swap hI]
  calc
    _ ≤ ∫ _ : AddCircle (1 : ℝ), (16 * p) ^ p ∂AddCircle.haarAddCircle :=
      integral_mono hI.integral_prod_right (integrable_const _) (fun θ => (hsection θ).2)
    _ = _ := by simp

end Erdos522
