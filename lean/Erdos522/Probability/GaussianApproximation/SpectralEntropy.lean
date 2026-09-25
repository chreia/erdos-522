/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.CovarianceChange
import Mathlib.Analysis.Matrix.PosDef

/-!
# Gaussian entropy controlled by covariance eigenvalues

Orthogonal diagonalization reduces a positive covariance matrix to independent
Gaussian coordinates. Quadratic form control around the identity therefore
gives a dimension-dependent relative entropy estimate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal MatrixOrder RealInnerProductSpace

namespace Erdos522

/-- Relative entropy from a positive Gaussian covariance to identity is bounded
by the sum of squared eigenvalue deviations. -/
theorem klDiv_multivariateGaussian_identity_le {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (heig : ∀ i, 1 / 2 ≤ hS.isHermitian.eigenvalues i) :
    klDiv (multivariateGaussian 0 S) (multivariateGaussian 0 (1 : Matrix (Fin n) (Fin n) ℝ)) ≤
      ENNReal.ofReal (∑ i, (hS.isHermitian.eigenvalues i - 1) ^ 2) := by
  let v : Fin n → ℝ≥0 := fun i => ⟨hS.isHermitian.eigenvalues i, (hS.eigenvalues_pos i).le⟩
  let U : Matrix (Fin n) (Fin n) ℝ := hS.isHermitian.eigenvectorUnitary
  have hv : ∀ i, v i ≠ 0 := by
    intro i
    exact ne_of_gt (show 0 < v i from hS.eigenvalues_pos i)
  have hspec : U * (Matrix.diagonal fun i => (v i : ℝ)) * U.conjTranspose = S := by
    change U * Matrix.diagonal hS.isHermitian.eigenvalues * star U = S
    exact hS.isHermitian.spectral_theorem.symm
  have hunit : U * (Matrix.diagonal fun _ : Fin n => (1 : ℝ)) * U.conjTranspose = 1 := by
    rw [Matrix.diagonal_one, mul_one]
    exact Unitary.coe_mul_star_self hS.isHermitian.eigenvectorUnitary
  have h := klDiv_gaussian_covariance_conjugate_le U v (fun _ => 1) hv (by simp)
    (by intro i; change 1 / 2 ≤ hS.isHermitian.eigenvalues i / 1; simpa only [div_one] using heig i)
  change klDiv (multivariateGaussian 0 (U * (Matrix.diagonal fun i => (v i : ℝ)) * U.conjTranspose))
      (multivariateGaussian 0 (U * (Matrix.diagonal fun _ => (1 : ℝ)) * U.conjTranspose)) ≤
    ENNReal.ofReal (∑ i, (hS.isHermitian.eigenvalues i / 1 - 1) ^ 2) at h
  simpa only [hspec, hunit, div_one] using h

/-- A quadratic form bound controls every eigenvalue deviation. -/
theorem eigenvalue_sub_one_le_of_quadratic_bound {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsHermitian) (ε : ℝ)
    (hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      |x.ofLp ⬝ᵥ S *ᵥ x.ofLp - ‖x‖ ^ 2| ≤ ε * ‖x‖ ^ 2) (i : Fin n) :
    |hS.eigenvalues i - 1| ≤ ε := by
  have h := hbound (hS.eigenvectorBasis i)
  have heig := hS.eigenvalues_eq i
  have hnorm := hS.eigenvectorBasis.orthonormal.1 i
  simp only [star_trivial, RCLike.re_to_real] at heig
  rw [← heig, hnorm] at h
  simpa using h

/-- Positive covariance matrices within relative quadratic error `ε ≤ 1/2`
have relative entropy at most `n ε²` from the identity covariance. -/
theorem klDiv_multivariateGaussian_identity_le_of_quadratic_bound {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (ε : ℝ)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      |x.ofLp ⬝ᵥ S *ᵥ x.ofLp - ‖x‖ ^ 2| ≤ ε * ‖x‖ ^ 2) :
    klDiv (multivariateGaussian 0 S) (multivariateGaussian 0 (1 : Matrix (Fin n) (Fin n) ℝ)) ≤
      ENNReal.ofReal ((n : ℝ) * ε ^ 2) := by
  have heig i := eigenvalue_sub_one_le_of_quadratic_bound S hS.isHermitian ε hbound i
  refine (klDiv_multivariateGaussian_identity_le S hS (fun i => ?_)).trans ?_
  · have h := (abs_le.mp (heig i)).1
    linarith
  · apply ENNReal.ofReal_le_ofReal
    calc
      ∑ i, (hS.isHermitian.eigenvalues i - 1) ^ 2 ≤ ∑ _ : Fin n, ε ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).mpr (heig i)
      _ = (n : ℝ) * ε ^ 2 := by simp

end Erdos522
