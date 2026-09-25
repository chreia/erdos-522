/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ComplexCoefficientVectorMoments
import Erdos522.Probability.GaussianApproximation.CircularCovarianceComparison

/-!
# Annular jet nondegeneracy for centered complex coefficients

Multiplication by a complex coefficient rotates and scales the real test
direction. Integrating the deterministic real Gram bound therefore preserves
its lower constant for every centered law of unit second moment.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- Complex multiplication scales the squared norm of a jet test direction. -/
theorem norm_sq_complex_jet_direction (c : ℂ) (x : EuclideanSpace ℝ (Fin 4)) :
    ‖c.re • x + c.im • jetDirectionRotation x‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, jetDirectionRotation, Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

/-- The same norm identity holds for a pair of jet directions. -/
theorem norm_sq_complex_paired_jet_direction (c : ℂ) (x : EuclideanSpace ℝ (Fin 8)) :
    ‖c.re • x + c.im • pairedJetDirectionRotation x‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.sum_univ_zero,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pairedJetDirectionRotation,
    Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

/-- Away from the real exceptional sectors, every centered unit-variance
complex coefficient law has the real jet covariance lower bound. -/
theorem covarianceBilin_complex_jet_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    (N : ℕ) (hN : 0 < N) (K r θ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 4)) :
    (Real.exp (-4 * K) / 80) * ‖x‖ ^ 2 ≤ covarianceBilin
      ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
        (circularJet N r (Complex.exp (Complex.I * θ)))) x x := by
  unfold circularJet
  apply covarianceBilin_complexCoefficientSum_lower μ h2 hmean hnorm
  intro c y
  have h := covarianceBilin_realRademacherJet_lower N hN K r θ hK hNK hrl hru hdegree hangle
    (c.re • y + c.im • jetDirectionRotation y)
  simp only [realRademacherJet, covarianceBilin_signVectorSum, ← sq,
    norm_sq_complex_jet_direction] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [circularVector, inner_add_right, real_inner_smul_right,
    inner_add_left, real_inner_smul_left, inner_imaginaryJetCoefficient_rotation]

/-- At separated points, every centered unit-variance complex law retains
the eight-dimensional lower covariance constant. -/
theorem covarianceBilin_complex_paired_jet_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 8)) :
    (Real.exp (-4 * K) / 160) * ‖x‖ ^ 2 ≤ covarianceBilin
      ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
        (circularPairedJet N r s (Complex.exp (Complex.I * θ))
          (Complex.exp (Complex.I * φ)))) x x := by
  unfold circularPairedJet
  apply covarianceBilin_complexCoefficientSum_lower μ h2 hmean hnorm
  intro c y
  have h := covarianceBilin_realPairedRademacherJet_lower N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum (c.re • y + c.im • pairedJetDirectionRotation y)
  simp only [realPairedRademacherJet, covarianceBilin_signVectorSum, ← sq,
    norm_sq_complex_paired_jet_direction] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [circularVector, inner_add_right, real_inner_smul_right,
    inner_add_left, real_inner_smul_left, inner_imaginaryPairedJetCoefficient]

end Erdos522
