/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianCoefficients
import Erdos522.Probability.GaussianApproximation.ComplexCoefficientVectors

/-!
# Gaussian vector sums with circular complex coefficients

Independence and real linearity identify every finite vector sum exactly with
the centered multivariate Gaussian having its actual covariance matrix.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- Each real linear image of an independent circular Gaussian coefficient is Gaussian. -/
theorem hasGaussianLaw_circularGaussian_coordinate {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) (k : Fin n) :
    HasGaussianLaw (fun ω : Fin n → ℂ => circularVector (a k) (b k) (ω k))
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) := by
  have heval := measurePreserving_eval (fun _ : Fin n => circularComplexGaussian) k
  have hcoord : HasGaussianLaw (fun ω : Fin n → ℂ => ω k)
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) :=
    (show HasLaw (fun ω : Fin n → ℂ => ω k) circularComplexGaussian
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) from
      ⟨heval.measurable.aemeasurable, heval.map_eq⟩).hasGaussianLaw
  exact HasGaussianLaw.map_of_measurable (complexCoefficientLinearMap (a k) (b k))
    hcoord (by fun_prop)

/-- Independent circular Gaussian vector sums have Gaussian law. -/
theorem hasGaussianLaw_circularGaussianVectorSum {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) :
    HasGaussianLaw (circularVectorSum a b)
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) := by
  have hind : iIndepFun (fun k (ω : Fin n → ℂ) => circularVector (a k) (b k) (ω k))
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) :=
    iIndepFun_pi (fun k => (show Measurable (circularVector (a k) (b k)) by
      unfold circularVector; fun_prop).aemeasurable)
  exact hind.hasGaussianLaw_fun_sum (hasGaussianLaw_circularGaussian_coordinate a b)

/-- These vector sums are centered. -/
theorem integral_circularGaussianVectorSum {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∫ ω, circularVectorSum a b ω ∂Measure.pi (fun _ : Fin n => circularComplexGaussian)) = 0 := by
  have hI (k : Fin n) : Integrable (fun ω : Fin n → ℂ => circularVector (a k) (b k) (ω k))
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) :=
    (hasGaussianLaw_circularGaussian_coordinate a b k).integrable
  simp only [circularVectorSum]
  rw [integral_finsetSum _ (fun k _ => hI k)]
  apply Finset.sum_eq_zero
  intro k _
  have heval := measurePreserving_eval (fun _ : Fin n => circularComplexGaussian) k
  have h := integral_complexCoefficientVector_eq_zero circularComplexGaussian
    IsGaussian.integrable_id integral_id_circularComplexGaussian (a k) (b k)
  rw [← heval.map_eq, integral_map heval.measurable.aemeasurable
    (by unfold circularVector; fun_prop)] at h
  exact h

/-- The exact multivariate Gaussian law, in the actual covariance normalization. -/
theorem map_circularGaussianVectorSum {n d : ℕ}
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) :
    (Measure.pi (fun _ : Fin n => circularComplexGaussian)).map (circularVectorSum a b) =
      multivariateGaussian 0 (coefficientCovarianceMatrix circularComplexGaussian a b) := by
  have : IsGaussian ((Measure.pi (fun _ : Fin n => circularComplexGaussian)).map
      (circularVectorSum a b)) := (hasGaussianLaw_circularGaussianVectorSum a b).isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map (by unfold circularVectorSum circularVector; fun_prop) (by fun_prop)]
    simpa only [id_eq, integral_id_multivariateGaussian] using integral_circularGaussianVectorSum a b
  · ext x y
    unfold coefficientCovarianceMatrix
    rw [covarianceBilin_multivariateGaussian (covarianceMatrix_posSemidef _),
      dotProduct_covarianceMatrix_mulVec]

end Erdos522
