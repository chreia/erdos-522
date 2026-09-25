/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.ComplexCoefficientVectors
import Erdos522.Probability.Covariance.ComplexCoefficientJets
import Erdos522.Probability.GaussianApproximation.CircularPairedJets

/-!
# Gaussian approximation for bounded complex polynomial jets

Unit coefficient second moment preserves the annular covariance constants.
The coefficient bound enters the approximation error only through its cube.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

private local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule

/-- The four-dimensional approximation constant for coefficients bounded by `B`. -/
def boundedJetGaussianErrorConstant (C B K : ℝ) : ℝ :=
  128 * C * (4 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 * Real.exp (3 * K) /
    Real.sqrt (Real.exp (-4 * K) / 80) ^ 3

/-- The eight-dimensional approximation constant for two separated jets. -/
def boundedPairedJetGaussianErrorConstant (C B K : ℝ) : ℝ :=
  1024 * C * (8 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 * Real.exp (3 * K) /
    Real.sqrt (Real.exp (-4 * K) / 160) ^ 3

/-- Actual bounded complex coefficient laws satisfy the four-dimensional
annular convex-set approximation. -/
theorem exists_gaussian_approximation_bounded_jet_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (B : ℝ) (_ : 0 ≤ B) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
      (_ : (∫ z, z ∂μ) = 0) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
      (N : ℕ) (_ : 0 < N) (K r θ : ℝ) (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (A : Set (EuclideanSpace ℝ (Fin 4))) (_ : MeasurableSet A) (_ : Convexity.IsConvexSet ℝ A),
      |(((Measure.pi (fun _ : Fin (N + 1) => μ)).map
          (circularJet N r (Complex.exp (Complex.I * θ)))) A).toReal -
        (multivariateGaussian 0 (coefficientCovarianceMatrix μ
          (realJetCoefficient N r (Complex.exp (Complex.I * θ)))
          (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ)))) A).toReal| ≤
        boundedJetGaussianErrorConstant C B K / Real.sqrt N := by
  obtain ⟨C, hC, happ⟩ := exists_gaussian_approximation_complex_coefficients_constant
  refine ⟨C, hC, ?_⟩
  intro μ _ B hB hb hm hv N hN K r θ hK hNK hrl hru hdegree hangle A hA hconvex
  have h2 : MemLp (fun z : ℂ => z) 2 μ := MemLp.of_bound (by fun_prop) B hb
  let z := Complex.exp (Complex.I * θ)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 ≤ r := by
    have hu : K / N ≤ (1 / 2 : ℝ) := (div_le_iff₀ hn).mpr (by linarith)
    linarith
  have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  have h := happ μ B hB hb hm (by norm_num : 0 < 4)
    (realJetCoefficient N r z) (imaginaryJetCoefficient N r z)
    (Real.exp (-4 * K) / 80) (by positivity)
    (covarianceBilin_complex_jet_lower μ h2 hm hv N hN K r θ hK hNK hrl hru hdegree hangle)
    A hA hconvex
  have hthird := circular_jet_third_moment_sum_le N hN K r hK hr hru z hz
  calc
    _ ≤ C * (4 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 *
        (∑ k, (‖realJetCoefficient N r z k‖ + ‖imaginaryJetCoefficient N r z k‖) ^ 3) /
          Real.sqrt (Real.exp (-4 * K) / 80) ^ 3 := h
    _ ≤ C * (4 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 *
        (128 * Real.exp (3 * K) / Real.sqrt N) /
          Real.sqrt (Real.exp (-4 * K) / 80) ^ 3 := by gcongr
    _ = _ := by unfold boundedJetGaussianErrorConstant; ring

/-- Actual bounded complex coefficient laws satisfy the eight-dimensional
convex-set approximation at separated annular points. -/
theorem exists_gaussian_approximation_bounded_paired_jet_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (B : ℝ) (_ : 0 ≤ B) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
      (_ : (∫ z, z ∂μ) = 0) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
      (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ) (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
      (A : Set (EuclideanSpace ℝ (Fin 8))) (_ : MeasurableSet A) (_ : Convexity.IsConvexSet ℝ A),
      |(((Measure.pi (fun _ : Fin (N + 1) => μ)).map
          (circularPairedJet N r s (Complex.exp (Complex.I * θ))
            (Complex.exp (Complex.I * φ)))) A).toReal -
        (multivariateGaussian 0 (coefficientCovarianceMatrix μ
          (realPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
          (imaginaryPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) A).toReal| ≤
        boundedPairedJetGaussianErrorConstant C B K / Real.sqrt N := by
  obtain ⟨C, hC, happ⟩ := exists_gaussian_approximation_complex_coefficients_constant
  refine ⟨C, hC, ?_⟩
  intro μ _ B hB hb hm hv N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdiff hsum A hA hconvex
  have h2 : MemLp (fun z : ℂ => z) 2 μ := MemLp.of_bound (by fun_prop) B hb
  let z := Complex.exp (Complex.I * θ)
  let w := Complex.exp (Complex.I * φ)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hfrac : K / N ≤ (1 / 2 : ℝ) := (div_le_iff₀ hn).mpr (by linarith)
  have hr : 0 ≤ r := by linarith
  have hs : 0 ≤ s := by linarith
  have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  have hw : ‖w‖ = 1 := by simp [w, Complex.norm_exp]
  have h := happ μ B hB hb hm (by norm_num : 0 < 8)
    (realPairedJetCoefficient N r s z w) (imaginaryPairedJetCoefficient N r s z w)
    (Real.exp (-4 * K) / 160) (by positivity)
    (covarianceBilin_complex_paired_jet_lower μ h2 hm hv N hN K r s θ φ hK hNK hrl hru hsl hsu
      hdegree hθ hφ hdiff hsum) A hA hconvex
  have hthird := circular_paired_jet_third_moment_sum_le N hN K r s hK hr hs hru hsu z w hz hw
  calc
    _ ≤ C * (8 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 *
        (∑ k, (‖realPairedJetCoefficient N r s z w k‖ +
          ‖imaginaryPairedJetCoefficient N r s z w k‖) ^ 3) /
          Real.sqrt (Real.exp (-4 * K) / 160) ^ 3 := h
    _ ≤ C * (8 : ℝ) ^ (1 / 4 : ℝ) * B ^ 3 *
        (1024 * Real.exp (3 * K) / Real.sqrt N) /
          Real.sqrt (Real.exp (-4 * K) / 160) ^ 3 := by gcongr
    _ = _ := by unfold boundedPairedJetGaussianErrorConstant; ring

end Erdos522
