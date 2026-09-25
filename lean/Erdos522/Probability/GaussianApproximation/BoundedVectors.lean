/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.Rademacher

/-!
# Gaussian approximation for bounded independent vectors

The covariance lower bound controls whitening, while deterministic bounds
on the summands control the third-moment term in Bentkus's theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder
namespace Erdos522

private local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- Whitening a bounded random vector gives an explicit third-moment bound. -/
theorem integral_third_norm_whitened_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : AEStronglyMeasurable X μ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) (c b : ℝ)
    (hc : 0 < c) (hbound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ b)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d), c * ‖x‖ ^ 2 ≤ x ⬝ᵥ S *ᵥ x) :
    (∫ ω, ‖inverseCovarianceSqrt S (X ω)‖ ^ 3 ∂μ) ≤ b ^ 3 / Real.sqrt c ^ 3 := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hpoint : ∀ᵐ ω ∂μ, ‖inverseCovarianceSqrt S (X ω)‖ ^ 3 ≤ (b / Real.sqrt c) ^ 3 := by
    filter_upwards [hbound] with ω hω
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_inverseCovarianceSqrt_le S hS c hc hlower (X ω)).trans
      (div_le_div_of_nonneg_right hω hs.le)
  have hmeas : AEStronglyMeasurable (fun ω => ‖inverseCovarianceSqrt S (X ω)‖ ^ 3) μ :=
    (((inverseCovarianceSqrt S).continuous.comp_aestronglyMeasurable hX).norm).pow 3
  have hint : Integrable (fun ω => ‖inverseCovarianceSqrt S (X ω)‖ ^ 3) μ :=
    (integrable_const ((b / Real.sqrt c) ^ 3)).mono' hmeas
      (hpoint.mono (fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
        exact hω))
  calc
    _ ≤ ∫ _ω, (b / Real.sqrt c) ^ 3 ∂μ := integral_mono_ae hint (integrable_const _) hpoint
    _ = b ^ 3 / Real.sqrt c ^ 3 := by simp [div_pow]

/-- A universal convex-set bound for centered, independent, bounded vectors. -/
theorem exists_gaussian_approximation_bounded_vectors_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {n d : ℕ} (_ : 0 < d)
      {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
      (_ : ∀ k, AEStronglyMeasurable (X k) μ)
      (_ : iIndepFun X μ) (_ : ∀ k, ∫ ω, X k ω ∂μ = 0)
      (b : Fin n → ℝ) (_ : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ b k)
      (S : Matrix (Fin d) (Fin d) ℝ) (_ : S.PosDef)
      (_ : ∀ x y, covarianceBilin (μ.map (fun ω => ∑ k, X k ω)) x y = x ⬝ᵥ S *ᵥ y)
      (c : ℝ) (_ : 0 < c)
      (_ : ∀ x : EuclideanSpace ℝ (Fin d), c * ‖x‖ ^ 2 ≤ x ⬝ᵥ S *ᵥ x)
      (A : Set (EuclideanSpace ℝ (Fin d))) (_ : MeasurableSet A)
      (_ : Convexity.IsConvexSet ℝ A),
      |((μ.map (fun ω => ∑ k, X k ω)) A).toReal -
        (multivariateGaussian 0 S A).toReal| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) * (∑ k, (b k) ^ 3) / Real.sqrt c ^ 3 := by
  obtain ⟨C, hC, happrox⟩ := exists_bentkus_convex_set_constant.{0}
  refine ⟨C, hC, ?_⟩
  intro n d hd Ω _ μ _ X hX hind hmean b hbound S hS hcov c hc hlower A hA hconvex
  have h3 (k : Fin n) : MemLp (X k) 3 μ := MemLp.of_bound (hX k) (b k) (hbound k)
  have hsum : (∑ k, ∫ ω, ‖inverseCovarianceSqrt S (X k ω)‖ ^ 3 ∂μ) ≤
      (∑ k, (b k) ^ 3) / Real.sqrt c ^ 3 := by
    calc
      _ ≤ ∑ k, (b k) ^ 3 / Real.sqrt c ^ 3 := Finset.sum_le_sum (fun k _ =>
        integral_third_norm_whitened_le μ (X k) (hX k) S hS c (b k) hc (hbound k) hlower)
      _ = _ := (Finset.sum_div _ _ _).symm
  calc
    _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ k, ∫ ω, ‖inverseCovarianceSqrt S (X k ω)‖ ^ 3 ∂μ :=
      happrox hd μ X S h3 hind hmean hS hcov A hA hconvex
    _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * ((∑ k, (b k) ^ 3) / Real.sqrt c ^ 3) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Erdos522
