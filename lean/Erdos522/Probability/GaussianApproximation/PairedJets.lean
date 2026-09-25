/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.Rademacher

/-!
# Gaussian approximation for separated pairs of jets

The paired covariance lower bound and coefficient third-moment estimate
give a uniform convex-set approximation in eight real dimensions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace MatrixOrder
namespace Erdos522
open LogMoments

local instance : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 8)) :=
  Convexity.ConvexSpace.ofModule

/-- The approximation constant for a pair of separated annular jets. -/
def pairedJetGaussianErrorConstant (C K : ℝ) : ℝ :=
  128 * C * (8 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K) /
    Real.sqrt (Real.exp (-4 * K) / 160) ^ 3

/-- The paired approximation constant is finite and positive. -/
theorem pairedJetGaussianErrorConstant_pos (C K : ℝ) (hC : 0 < C) :
    0 < pairedJetGaussianErrorConstant C K := by
  unfold pairedJetGaussianErrorConstant
  positivity

/-- The actual paired jet covariance is positive definite at separated annular points. -/
theorem realPairedJetCovarianceMatrix_posDef (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖) :
    (signCovarianceMatrix (realPairedJetCoefficient N r s
      (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).PosDef := by
  apply signCovarianceMatrix_posDef _ (Real.exp (-4 * K) / 160) (by positivity)
  intro x
  exact covarianceBilin_realPairedRademacherJet_lower N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum x

/-- Convex-set Gaussian approximation for the pair of normalized Rademacher jets,
using its actual covariance and the same coefficient signs at both points. -/
theorem exists_gaussian_approximation_paired_annular_jet_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
      (A : Set (EuclideanSpace ℝ (Fin 8))) (_ : MeasurableSet A)
      (_ : Convexity.IsConvexSet ℝ A),
      |(((signMeasure N).map (realPairedRademacherJet N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) A).toReal -
        (multivariateGaussian 0 (signCovarianceMatrix (realPairedJetCoefficient N r s
          (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) A).toReal| ≤
      pairedJetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_approximation_sign_sum_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A hA hconvex
  let a := realPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))
  let S := signCovarianceMatrix a
  let c := Real.exp (-4 * K) / 160
  have hc : 0 < c := by dsimp [c]; positivity
  have hS : S.PosDef := realPairedJetCovarianceMatrix_posDef N hN K r s θ φ hK hNK
    hrl hru hsl hsu hdegree hθ hφ hdifference hsum
  have hlower (x : EuclideanSpace ℝ (Fin 8)) : c * ‖x‖ ^ 2 ≤ x ⬝ᵥ S *ᵥ x := by
    rw [show S = covarianceMatrix ((signMeasure N).map (realPairedRademacherJet N r s
      (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) from rfl,
      dotProduct_covarianceMatrix_mulVec]
    exact covarianceBilin_realPairedRademacherJet_lower N hN K r s θ φ hK hNK hrl hru hsl hsu
      hdegree hθ hφ hdifference hsum x
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hmoment := sum_third_norm_realPairedJetCoefficient_le N hN K r s hK hr0 hs0 hru hsu
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))
    (Complex.norm_exp_I_mul_ofReal θ) (Complex.norm_exp_I_mul_ofReal φ)
  have hwhite := sum_third_norm_inverseCovarianceSqrt_le a S hS c hc hlower
  have hthird : (∑ k, ‖inverseCovarianceSqrt S (a k)‖ ^ 3) ≤
      (128 * Real.exp (3 * K) / Real.sqrt N) / Real.sqrt c ^ 3 :=
    hwhite.trans (div_le_div_of_nonneg_right hmoment (by positivity))
  have h := hbound (by omega : 0 < 8) a hS A hA hconvex
  calc
    _ ≤ C * (8 : ℝ) ^ (1 / 4 : ℝ) * ∑ k, ‖inverseCovarianceSqrt S (a k)‖ ^ 3 := h
    _ ≤ C * (8 : ℝ) ^ (1 / 4 : ℝ) *
        ((128 * Real.exp (3 * K) / Real.sqrt N) / Real.sqrt c ^ 3) :=
      mul_le_mul_of_nonneg_left hthird (by positivity)
    _ = pairedJetGaussianErrorConstant C K / Real.sqrt N := by
      unfold pairedJetGaussianErrorConstant
      dsimp [c]
      ring

end Erdos522
