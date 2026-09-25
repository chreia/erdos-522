/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.CircularPairedJets

/-!
# Gaussian approximation for paired circular jets

The separated-pair covariance bound and coefficient third moments give an
explicit eight-dimensional convex-set approximation under the shared
Steinhaus coefficient law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

private local instance : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 8)) :=
  Convexity.ConvexSpace.ofModule

/-- The finite approximation constant for a separated circular jet pair. -/
def circularPairedJetGaussianErrorConstant (C K : ℝ) : ℝ :=
  1024 * C * (8 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K) /
    Real.sqrt (Real.exp (-4 * K) / 160) ^ 3

theorem circularPairedJetGaussianErrorConstant_pos (C K : ℝ) (hC : 0 < C) :
    0 < circularPairedJetGaussianErrorConstant C K := by
  unfold circularPairedJetGaussianErrorConstant
  positivity

/-- The paired circular coefficient third moments retain the inverse-square-root
degree scale, with factor eight from the two real coefficient coordinates. -/
theorem circular_paired_jet_third_moment_sum_le (N : ℕ) (hN : 0 < N) (K r s : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hru : r ≤ 1 + K / N) (hsu : s ≤ 1 + K / N)
    (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    (∑ k, (‖realPairedJetCoefficient N r s z w k‖ +
      ‖imaginaryPairedJetCoefficient N r s z w k‖) ^ 3) ≤
        1024 * Real.exp (3 * K) / Real.sqrt N := by
  simp_rw [norm_imaginaryPairedJetCoefficient]
  have heq (t : ℝ) : (t + t) ^ 3 = 8 * t ^ 3 := by ring
  simp_rw [heq]
  rw [← Finset.mul_sum]
  calc
    _ ≤ 8 * (128 * Real.exp (3 * K) / Real.sqrt N) :=
      mul_le_mul_of_nonneg_left
        (sum_third_norm_realPairedJetCoefficient_le N hN K r s hK hr0 hs0 hru hsu z w hz hw)
        (by norm_num)
    _ = _ := by ring

/-- Positive definiteness of the actual paired circular covariance. -/
theorem circularPairedJetCovarianceMatrix_posDef (N : ℕ) (hN : 0 < N)
    (K r s θ φ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖) :
    (circularCovarianceMatrix
      (realPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
      (imaginaryPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).PosDef := by
  exact circularCovarianceMatrix_posDef _ _ (Real.exp (-4 * K) / 160) (by positivity)
    (circular_paired_jet_gram_lower N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum)

/-- Convex-set approximation of both jets from the same Steinhaus sequence. -/
theorem exists_gaussian_approximation_circular_paired_jet_constant :
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
      |(((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
        (circularPairedJet N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) A).toReal -
        (multivariateGaussian 0 (circularCovarianceMatrix
          (realPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
          (imaginaryPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) A).toReal| ≤
      circularPairedJetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, happrox⟩ := exists_gaussian_approximation_circular_vectors_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A hA hconvex
  let a := realPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))
  let b := imaginaryPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))
  let c := Real.exp (-4 * K) / 160
  have hc : 0 < c := by dsimp [c]; positivity
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hgram := circular_paired_jet_gram_lower N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum
  have h := happrox (by norm_num : 0 < 8) a b c hc hgram A hA hconvex
  have hthird := circular_paired_jet_third_moment_sum_le N hN K r s hK hr0 hs0 hru hsu
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))
    (Complex.norm_exp_I_mul_ofReal θ) (Complex.norm_exp_I_mul_ofReal φ)
  calc
    _ ≤ C * (8 : ℝ) ^ (1 / 4 : ℝ) * (∑ k, (‖a k‖ + ‖b k‖) ^ 3) / Real.sqrt c ^ 3 := h
    _ ≤ C * (8 : ℝ) ^ (1 / 4 : ℝ) *
        (1024 * Real.exp (3 * K) / Real.sqrt N) / Real.sqrt c ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hthird (by positivity)) (by positivity)
    _ = circularPairedJetGaussianErrorConstant C K / Real.sqrt N := by
      unfold circularPairedJetGaussianErrorConstant
      dsimp [c]
      ring

end Erdos522
