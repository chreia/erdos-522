/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianVectors
import Erdos522.Probability.GaussianApproximation.BoundedPairedSmallBall

/-!
# Exact Gaussian estimates for circular polynomial jets

The value and radial derivative are a linear image of the common circular
Gaussian coefficients. Their exact Gaussian law gives the product small-ball
scale, and covariance comparison controls separated pairs.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped NNReal RealInnerProductSpace
namespace Erdos522

/-- The annular jet is exactly a centered Gaussian vector with its coefficient covariance. -/
theorem map_circularGaussianJet (N : ℕ) (r : ℝ) (z : ℂ) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).map (circularJet N r z) =
      multivariateGaussian 0 (coefficientCovarianceMatrix circularComplexGaussian
        (realJetCoefficient N r z) (imaginaryJetCoefficient N r z)) := by
  exact map_circularGaussianVectorSum _ _

/-- The paired jets retain the covariance created by their shared coefficients. -/
theorem map_circularGaussianPairedJet (N : ℕ) (r s : ℝ) (z w : ℂ) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).map
      (circularPairedJet N r s z w) =
      multivariateGaussian 0 (coefficientCovarianceMatrix circularComplexGaussian
        (realPairedJetCoefficient N r s z w) (imaginaryPairedJetCoefficient N r s z w)) := by
  exact map_circularGaussianVectorSum _ _

/-- Retained circular Gaussian polynomial jets have the exact two-disk small-ball scale. -/
theorem circularGaussian_annular_polynomial_small_ball (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v) ≤
      u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) := by
  let z := Complex.exp (Complex.I * θ)
  let S := coefficientCovarianceMatrix circularComplexGaussian
    (realJetCoefficient N r z) (imaginaryJetCoefficient N r z)
  let c : ℝ≥0 := ⟨Real.exp (-4 * K) / 80, by positivity⟩
  have hc : c ≠ 0 := ne_of_gt (show 0 < c from by
    change 0 < Real.exp (-4 * K) / 80
    positivity)
  have hcov := covarianceBilin_complex_jet_lower circularComplexGaussian
    memLp_two_id_circularComplexGaussian integral_id_circularComplexGaussian
    integral_norm_sq_circularComplexGaussian N hN K r θ hK hNK hrl hru hdegree hangle
  have hS : S.PosDef := coefficientCovarianceMatrix_posDef circularComplexGaussian _ _
    (by positivity) hcov
  have hlower (x : EuclideanSpace ℝ (Fin 4)) : (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
    change (Real.exp (-4 * K) / 80) * ‖x‖ ^ 2 ≤ _
    rw [show S = coefficientCovarianceMatrix circularComplexGaussian
      (realJetCoefficient N r z) (imaginaryJetCoefficient N r z) from rfl,
      coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec]
    exact hcov x
  have hb := gaussian_jetSmallBallSet_le S hS.posSemidef c hc hlower u v hu hv
  rw [← map_circularGaussianJet N r z, coefficientJet_measureReal_smallBall _ N hN] at hb
  exact hb

/-- Separated circular Gaussian polynomial jets approximately factor with the explicit
covariance-comparison constant and no additive central-limit error. -/
theorem circularGaussian_polynomial_small_ball_factorization (N : ℕ) (hN : 0 < N)
    (K r s θ φ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖) (u v u' v' : ℝ) :
    |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v ∩
        circularPolynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v') -
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
        (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v) *
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
        (circularPolynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v')| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  have hb := gaussian_complexPairedJet_measureReal_prod_le circularComplexGaussian
    memLp_two_id_circularComplexGaussian integral_id_circularComplexGaussian
    integral_norm_sq_circularComplexGaussian N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum (jetSmallBallSet u v) (jetSmallBallSet u' v')
    (measurableSet_jetSmallBallSet u v) (measurableSet_jetSmallBallSet u' v')
  rw [← map_circularGaussianPairedJet, ← map_circularGaussianJet, ← map_circularGaussianJet,
    coefficientPairedJet_measureReal_smallBall _ N hN,
    coefficientJet_measureReal_smallBall _ N hN, coefficientJet_measureReal_smallBall _ N hN] at hb
  exact hb

end Erdos522
