/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.CircularJets

/-!
# Gaussian approximation of circular jets

The angularly uniform covariance bound and the annular coefficient norms
give an explicit inverse-square-root-degree error for Steinhaus jets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

private local instance : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Convexity.ConvexSpace.ofModule

/-- The finite constant in the circular jet approximation. -/
def circularJetGaussianErrorConstant (C K : ℝ) : ℝ :=
  128 * C * (4 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K) /
    Real.sqrt (Real.exp (-4 * K) / 32) ^ 3

/-- The circular jet has the same annular third-moment scale at every angle. -/
theorem circular_jet_third_moment_sum_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hru : r ≤ 1 + K / N)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ k, (‖realJetCoefficient N r z k‖ + ‖imaginaryJetCoefficient N r z k‖) ^ 3) ≤
      128 * Real.exp (3 * K) / Real.sqrt N := by
  simp_rw [norm_imaginaryJetCoefficient]
  have heq (t : ℝ) : (t + t) ^ 3 = 8 * t ^ 3 := by ring
  simp_rw [heq]
  rw [← Finset.mul_sum]
  calc
    _ ≤ 8 * (16 * Real.exp (3 * K) / Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (sum_third_norm_realJetCoefficient_le N hN K r hK hr0 hru z hz)
        (by norm_num)
    _ = _ := by ring

/-- The circular coefficient Gram form is uniformly nondegenerate in the annulus. -/
theorem circular_jet_gram_lower (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hrl : 1 - K / N ≤ r)
    (z : ℂ) (hz : ‖z‖ = 1) (x : EuclideanSpace ℝ (Fin 4)) :
    (Real.exp (-4 * K) / 32) * ‖x‖ ^ 2 ≤
      ∑ k, (⟪x, realJetCoefficient N r z k⟫ ^ 2 +
        ⟪x, imaginaryJetCoefficient N r z k⟫ ^ 2) / 2 := by
  have h := annular_circular_jet_nondegeneracy N hN K r hK hNK hrl z hz x
  simpa only [circularJet, covarianceBilin_circularVectorSum, sq] using h

/-- Convex-set Gaussian approximation for the actual Steinhaus jet law. -/
theorem exists_gaussian_approximation_circular_jet_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (z : ℂ) (_ : ‖z‖ = 1) (A : Set (EuclideanSpace ℝ (Fin 4)))
      (_ : MeasurableSet A) (_ : Convexity.IsConvexSet ℝ A),
      |(((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularJet N r z)) A).toReal -
        (multivariateGaussian 0 (circularCovarianceMatrix
          (realJetCoefficient N r z) (imaginaryJetCoefficient N r z)) A).toReal| ≤
      circularJetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, happrox⟩ := exists_gaussian_approximation_circular_vectors_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru z hz A hA hconvex
  let c := Real.exp (-4 * K) / 32
  have hc : 0 < c := by dsimp [c]; positivity
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ r := by
    have hu : K / N ≤ (1 / 2 : ℝ) := (div_le_iff₀ hn).mpr (by linarith)
    linarith
  have hgram := circular_jet_gram_lower N hN K r hK hNK hrl z hz
  have h := happrox (by norm_num : 0 < 4) (realJetCoefficient N r z)
    (imaginaryJetCoefficient N r z) c hc hgram A hA hconvex
  have hthird := circular_jet_third_moment_sum_le N hN K r hK hr0 hru z hz
  calc
    _ ≤ C * (4 : ℝ) ^ (1 / 4 : ℝ) *
        (∑ k, (‖realJetCoefficient N r z k‖ + ‖imaginaryJetCoefficient N r z k‖) ^ 3) /
          Real.sqrt c ^ 3 := h
    _ ≤ C * (4 : ℝ) ^ (1 / 4 : ℝ) *
        (128 * Real.exp (3 * K) / Real.sqrt N) / Real.sqrt c ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hthird (by positivity)) (by positivity)
    _ = circularJetGaussianErrorConstant C K / Real.sqrt N := by
      unfold circularJetGaussianErrorConstant
      dsimp [c]
      ring

end Erdos522
