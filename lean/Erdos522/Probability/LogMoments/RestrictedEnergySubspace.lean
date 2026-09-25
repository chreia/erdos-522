/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.SpectralTruncation
import Erdos522.Probability.LogMoments.RestrictedFourierEnergy

/-!
# Spectral subspaces for restricted Rademacher Fourier energy

The Hilbert–Schmidt estimate bounds the number of negative eigenvalues that can
obstruct coercivity of the restricted Gram matrix.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexInnerProductSpace

namespace Erdos522.LogMoments

/-- The squared Hilbert–Schmidt estimate, with the measure exponent explicit. -/
theorem restrictedPairMatrix_sum_sq_le {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (m : ℕ) (hm : 1 ≤ m) :
    (∑ i, ∑ j, ‖restrictedPairMatrix E i j‖ ^ 2) ≤
      (16 * Real.exp 2 * (m : ℝ)) ^ 2 *
        (fourierMeasure N).real E ^ (2 - 1 / (m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h := restrictedPairMatrix_hilbertSchmidt_le E m hm
  have hnon : 0 ≤ ∑ i, ∑ j, ‖restrictedPairMatrix E i j‖ ^ 2 := by positivity
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr h
  rw [Real.sq_sqrt hnon, mul_pow] at hsq
  have hexp : (1 - 1 / (2 * (m : ℝ))) * (2 : ℕ) = 2 - 1 / (m : ℝ) := by
    push_cast
    field_simp
  rwa [← Real.rpow_mul_natCast measureReal_nonneg, hexp] at hsq

private theorem dimension_bound_simplify {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    4 * ((16 * Real.exp 2 * (m : ℝ)) ^ 2 * δ ^ (2 - 1 / (m : ℝ))) / δ ^ 2 =
      (32 * Real.exp 2 * (m : ℝ)) ^ 2 * δ ^ (-(1 / (m : ℝ))) := by
  rw [Real.rpow_sub hδ, Real.rpow_two, Real.rpow_neg hδ.le]
  field_simp
  ring

/-- Outside a subspace of dimension `O(m² μ(E)^(-1/m))`, the restricted Gram
    matrix is bounded below by half its scalar part. -/
theorem exists_subspace_restricted_matrix_coercive {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (hE : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m) :
    ∃ V : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1))),
      (Module.finrank ℂ V : ℝ) ≤
        (32 * Real.exp 2 * (m : ℝ)) ^ 2 *
          (fourierMeasure N).real E ^ (-(1 / (m : ℝ))) ∧
      ∀ x ∈ Vᗮ, ((fourierMeasure N).real E / 2) * ‖x‖ ^ 2 ≤
        (fourierMeasure N).real E * ‖x‖ ^ 2 +
          (⟪x, (restrictedPairMatrix E).toEuclideanLin x⟫).re := by
  obtain ⟨V, hdim, hform⟩ := exists_subspace_matrix_shift_coercive
    (restrictedPairMatrix E) (restrictedPairMatrix_isHermitian E) hE
    (restrictedPairMatrix_sum_sq_le E m hm)
  exact ⟨V, (dimension_bound_simplify hE m) ▸ hdim, hform⟩

/-- A coefficient-uniform coercive subspace for actual restricted Fourier energy. -/
theorem exists_restricted_energy_subspace {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (hE : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m) :
    ∃ V : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1))),
      (Module.finrank ℂ V : ℝ) ≤
        (32 * Real.exp 2 * (m : ℝ)) ^ 2 *
          (fourierMeasure N).real E ^ (-(1 / (m : ℝ))) ∧
      ∀ a ∈ Vᗮ, ((fourierMeasure N).real E / 2) * (∑ k, ‖a k‖ ^ 2) ≤
        ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  obtain ⟨V, hdim, hform⟩ := exists_subspace_restricted_matrix_coercive E hE m hm
  refine ⟨V, hdim, ?_⟩
  intro a ha
  rw [integral_norm_sq_randomFourier_eq_matrix]
  simpa only [EuclideanSpace.norm_sq_eq] using hform a ha

end Erdos522.LogMoments
