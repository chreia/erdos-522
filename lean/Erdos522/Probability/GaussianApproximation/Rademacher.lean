/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.JetMoments
import ProbabilityApproximation.Bentkus.Induction

/-!
# Gaussian approximation for finite Rademacher sums

Bentkus's theorem supplies a universal finite constant. For a sum of signs
multiplied by deterministic vectors, its whitened third-moment term is an
explicit finite sum of coefficient norms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace MatrixOrder
namespace Erdos522
open LogMoments

local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- The covariance matrix of a vector sign sum in the canonical orthonormal basis. -/
def signCovarianceMatrix {N d : ℕ} (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ := covarianceMatrix ((signMeasure N).map (signVectorSum a))

/-- The covariance matrix is characterized by its Gram bilinear form. -/
theorem signCovarianceMatrix_form {N d : ℕ}
    (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d)) (x y : EuclideanSpace ℝ (Fin d)) :
    x ⬝ᵥ signCovarianceMatrix a *ᵥ y = ∑ k, ⟪x, a k⟫ * ⟪y, a k⟫ := by
  rw [signCovarianceMatrix, dotProduct_covarianceMatrix_mulVec, covarianceBilin_signVectorSum]

/-- A strictly positive covariance form gives a positive definite covariance matrix. -/
theorem signCovarianceMatrix_posDef {N d : ℕ}
    (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d)) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ covarianceBilin ((signMeasure N).map (signVectorSum a)) x x) :
    (signCovarianceMatrix a).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (covarianceMatrix_posSemidef _).isHermitian
  intro x hx
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  have hy : y ≠ 0 := by
    intro he
    apply hx
    exact congrArg WithLp.ofLp he
  have h := hlower y
  have hp : 0 < c * ‖y‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.mpr hy) 2)
  have hf := dotProduct_covarianceMatrix_mulVec ((signMeasure N).map (signVectorSum a)) y y
  rw [← hf] at h
  simpa only [star_trivial, signCovarianceMatrix, y] using (hp.trans_le h)

/-- Applying deterministic vector maps preserves independence of the coordinate signs. -/
theorem iIndepFun_sign_summands {N d : ℕ} (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun k (ω : SignVector N) => realSign (ω k) • a k) (signMeasure N) := by
  exact (iIndepFun_realSign N).comp (fun k t => t • a k) (by intro k; fun_prop)

/-- Each vector sign summand is centered. -/
theorem integral_sign_summand {N d : ℕ} (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
    (k : Fin (N + 1)) :
    (∫ ω : SignVector N, realSign (ω k) • a k ∂signMeasure N) = 0 := by
  rw [integral_smul_const, integral_realSign_coordinate, zero_smul]

/-- Whitening commutes with a sign and removes its modulus from third moments. -/
theorem integral_third_norm_whitened_sign {N d : ℕ}
    (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (k : Fin (N + 1)) :
    (∫ ω : SignVector N, ‖T (realSign (ω k) • a k)‖ ^ 3 ∂signMeasure N) = ‖T (a k)‖ ^ 3 := by
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_realSign, one_mul, integral_const,
    probReal_univ, one_smul]

/-- A universal convex-set Gaussian approximation bound for finite vector sign sums. -/
theorem exists_gaussian_approximation_sign_sum_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {N d : ℕ} (_ : 0 < d)
      (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
      (_ : (signCovarianceMatrix a).PosDef)
      (A : Set (EuclideanSpace ℝ (Fin d))) (_ : MeasurableSet A)
      (_ : Convexity.IsConvexSet ℝ A),
      |(((signMeasure N).map (signVectorSum a)) A).toReal -
        (multivariateGaussian 0 (signCovarianceMatrix a) A).toReal| ≤
      C * (d : ℝ) ^ (1 / 4 : ℝ) * ∑ k,
        ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (signCovarianceMatrix a))⁻¹) (a k)‖ ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := exists_bentkus_convex_set_constant.{0}
  refine ⟨C, hC, ?_⟩
  intro N d hd a hS A hA hconvex
  have hcov (x y : EuclideanSpace ℝ (Fin d)) :
      covarianceBilin ((signMeasure N).map
        (fun ω => ∑ k, realSign (ω k) • a k)) x y = x ⬝ᵥ signCovarianceMatrix a *ᵥ y :=
    (dotProduct_covarianceMatrix_mulVec _ x y).symm
  have h := hbound hd (signMeasure N) (fun k ω => realSign (ω k) • a k)
    (signCovarianceMatrix a) (fun _ => MemLp.of_discrete)
    (iIndepFun_sign_summands a) (integral_sign_summand a) hS hcov A hA hconvex
  simp only [integral_third_norm_whitened_sign] at h
  exact h

/-- The inverse positive square root of a covariance matrix as a Euclidean linear map. -/
def inverseCovarianceSqrt {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹

/-- A covariance lower bound controls the inverse-square-root map. -/
theorem norm_inverseCovarianceSqrt_le {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d), c * ‖x‖ ^ 2 ≤ x ⬝ᵥ S *ᵥ x)
    (x : EuclideanSpace ℝ (Fin d)) : ‖inverseCovarianceSqrt S x‖ ≤ ‖x‖ / Real.sqrt c := by
  change ‖bentkusWhiteningCLM S x‖ ≤ ‖x‖ / Real.sqrt c
  have h := hlower (bentkusWhiteningCLM S x)
  rw [← inner_toEuclideanCLM] at h
  have he : ⟪bentkusWhiteningCLM S x,
      toEuclideanCLM (𝕜 := ℝ) S (bentkusWhiteningCLM S x)⟫ = ‖x‖ ^ 2 := by
    calc
      _ = ⟪x, bentkusWhiteningCLM S
          (toEuclideanCLM (𝕜 := ℝ) S (bentkusWhiteningCLM S x))⟫ := by
        nth_rw 1 [← adjoint_bentkusWhiteningCLM S]
        exact (bentkusWhiteningCLM S).adjoint_inner_left _ _
      _ = ‖x‖ ^ 2 := by rw [bentkusWhiteningCLM_covariance_comp d S hS, real_inner_self_eq_norm_sq]
  rw [he] at h
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  apply (le_div_iff₀ hs).mpr
  have hsq := Real.sq_sqrt hc.le
  have hnorm := norm_nonneg (bentkusWhiteningCLM S x)
  have hmul : (‖bentkusWhiteningCLM S x‖ * Real.sqrt c) ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith only [h, hsq]
  nlinarith [norm_nonneg x, mul_nonneg hnorm hs.le]

/-- The covariance matrix of one annular Rademacher jet is positive definite. -/
theorem realJetCovarianceMatrix_posDef (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖) :
    (signCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ)))).PosDef := by
  apply signCovarianceMatrix_posDef _ (Real.exp (-4 * K) / 80) (by positivity)
  intro x
  exact covarianceBilin_realRademacherJet_lower N hN K r θ hK hNK hrl hru hdegree hangle x

/-- A lower covariance bound controls the complete whitened third-moment sum. -/
theorem sum_third_norm_inverseCovarianceSqrt_le {N d : ℕ}
    (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d), c * ‖x‖ ^ 2 ≤ x ⬝ᵥ S *ᵥ x) :
    (∑ k, ‖inverseCovarianceSqrt S (a k)‖ ^ 3) ≤
      (∑ k, ‖a k‖ ^ 3) / Real.sqrt c ^ 3 := by
  calc
    _ ≤ ∑ k, (‖a k‖ / Real.sqrt c) ^ 3 :=
      Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _)
        (norm_inverseCovarianceSqrt_le S hS c hc hlower (a k)) 3)
    _ = _ := by simp only [div_pow, ← Finset.sum_div]

/-- The one-point Gaussian approximation constant, expressed in terms of
Bentkus's universal constant and the annular covariance lower bound. -/
def jetGaussianErrorConstant (C K : ℝ) : ℝ :=
  16 * C * (4 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K) /
    Real.sqrt (Real.exp (-4 * K) / 80) ^ 3

/-- Every positive Bentkus constant gives a finite positive annular error constant. -/
theorem jetGaussianErrorConstant_pos (C K : ℝ) (hC : 0 < C) :
    0 < jetGaussianErrorConstant C K := by
  unfold jetGaussianErrorConstant
  positivity

/-- Convex-set Gaussian approximation for one annular normalized Rademacher jet,
with error of order `N⁻¹ᐟ²` and the actual covariance matrix. -/
theorem exists_gaussian_approximation_annular_jet_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r θ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (A : Set (EuclideanSpace ℝ (Fin 4))) (_ : MeasurableSet A)
      (_ : Convexity.IsConvexSet ℝ A),
      |(((signMeasure N).map (realRademacherJet N r (Complex.exp (Complex.I * θ)))) A).toReal -
        (multivariateGaussian 0
          (signCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ)))) A).toReal| ≤
      jetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_approximation_sign_sum_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r θ hK hNK hrl hru hdegree hangle A hA hconvex
  let a := realJetCoefficient N r (Complex.exp (Complex.I * θ))
  let S := signCovarianceMatrix a
  let c := Real.exp (-4 * K) / 80
  have hc : 0 < c := by dsimp [c]; positivity
  have hS : S.PosDef := realJetCovarianceMatrix_posDef N hN K r θ hK hNK hrl hru hdegree hangle
  have hlower (x : EuclideanSpace ℝ (Fin 4)) : c * ‖x‖ ^ 2 ≤ x ⬝ᵥ S *ᵥ x := by
    rw [show S = covarianceMatrix ((signMeasure N).map (realRademacherJet N r
      (Complex.exp (Complex.I * θ)))) from rfl, dotProduct_covarianceMatrix_mulVec]
    exact covarianceBilin_realRademacherJet_lower N hN K r θ hK hNK hrl hru hdegree hangle x
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hmoment := sum_third_norm_realJetCoefficient_le N hN K r hK hr0 hru
    (Complex.exp (Complex.I * θ)) (Complex.norm_exp_I_mul_ofReal θ)
  have hwhite := sum_third_norm_inverseCovarianceSqrt_le a S hS c hc hlower
  have hthird : (∑ k, ‖inverseCovarianceSqrt S (a k)‖ ^ 3) ≤
      (16 * Real.exp (3 * K) / Real.sqrt N) / Real.sqrt c ^ 3 :=
    hwhite.trans (div_le_div_of_nonneg_right hmoment (by positivity))
  have h := hbound (by omega : 0 < 4) a hS A hA hconvex
  calc
    _ ≤ C * (4 : ℝ) ^ (1 / 4 : ℝ) * ∑ k, ‖inverseCovarianceSqrt S (a k)‖ ^ 3 := h
    _ ≤ C * (4 : ℝ) ^ (1 / 4 : ℝ) *
        ((16 * Real.exp (3 * K) / Real.sqrt N) / Real.sqrt c ^ 3) :=
      mul_le_mul_of_nonneg_left hthird (by positivity)
    _ = jetGaussianErrorConstant C K / Real.sqrt N := by
      unfold jetGaussianErrorConstant
      dsimp [c]
      ring

end Erdos522
