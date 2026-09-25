/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.RestrictedFourierEnergy
import Erdos522.Probability.LogMoments.CenteredPairBessel

/-!
# Restricted Fourier energy on sets of large measure

A Hilbert–Schmidt estimate for the centered restricted Gram matrix controls its
entire quadratic form.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexInnerProductSpace

namespace Erdos522.LogMoments

/-- The operator norm of a complex matrix is at most its Hilbert–Schmidt norm. -/
theorem norm_toEuclideanCLM_le_sqrt_sum_sq_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hS]
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  rw [hx, Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ i, (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      simpa only [Matrix.mulVec, dotProduct, norm_mul] using
        norm_sum_le Finset.univ (fun j => A i j * x.ofLp j)
    _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 := by
      exact Finset.sum_le_sum (fun i _ =>
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖)
          (fun j => ‖x.ofLp j‖))
    _ = _ := by rw [← Finset.sum_mul]

/-- The real part of a matrix quadratic form is controlled by its Hilbert–Schmidt norm. -/
theorem abs_re_inner_matrix_le_hilbertSchmidt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    |(⟪x, A.toEuclideanLin x⟫).re| ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := by
  have hnorm : ‖A.toEuclideanLin x‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) * ‖x‖ := by
    exact (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right (norm_toEuclideanCLM_le_sqrt_sum_sq_norm A)
        (norm_nonneg x))
  calc
    _ ≤ ‖⟪x, A.toEuclideanLin x⟫‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖A.toEuclideanLin x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) * ‖x‖) := by gcongr
    _ = _ := by ring

/-- A scalar part of at least `9/10` dominates a matrix with the variance-scale
    Hilbert–Schmidt bound. -/
theorem norm_sq_le_two_matrix_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {δ : ℝ} (hδ : 9 / 10 ≤ δ) (hδ1 : δ ≤ 1)
    (hA : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ δ * (1 - δ)) (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 ≤ 2 * (δ * ‖x‖ ^ 2 + (⟪x, A.toEuclideanLin x⟫).re) := by
  let S : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsmall : S ≤ 1 / 10 := by
    calc
      S ≤ δ * (1 - δ) := hA
      _ ≤ 1 * (1 - δ) := mul_le_mul_of_nonneg_right hδ1 (sub_nonneg.mpr hδ1)
      _ ≤ 1 / 10 := by linarith
  have hsqrt : Real.sqrt S ≤ 2 / 5 := by
    have hsq := Real.sq_sqrt hS
    have hnon := Real.sqrt_nonneg S
    nlinarith
  have hinner := (abs_le.mp (abs_re_inner_matrix_le_hilbertSchmidt A x)).1
  have hloss : Real.sqrt S * ‖x‖ ^ 2 ≤ (2 / 5) * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hsqrt (sq_nonneg _)
  have hscalar : (9 / 10) * ‖x‖ ^ 2 ≤ δ * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hδ (sq_nonneg _)
  change -(Real.sqrt S * ‖x‖ ^ 2) ≤ _ at hinner
  linarith

/-- A set of probability at least `9/10` captures at least half the energy of
    every finite Rademacher Fourier sum, uniformly over all coefficients. -/
theorem coefficient_energy_le_twice_restricted_energy {N : ℕ}
    (a : Fin (N + 1) → ℂ) (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (hE : MeasurableSet E) (hlarge : 9 / 10 ≤ (fourierMeasure N).real E) :
    (∑ k, ‖a k‖ ^ 2) ≤ 2 * ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  rw [integral_norm_sq_randomFourier_eq_matrix]
  have h := norm_sq_le_two_matrix_energy (restrictedPairMatrix E) hlarge
    measureReal_le_one (restrictedPairMatrix_hilbertSchmidt_sq_le_variance E hE)
    (WithLp.toLp 2 a)
  simpa only [EuclideanSpace.norm_sq_eq] using h

end Erdos522.LogMoments
