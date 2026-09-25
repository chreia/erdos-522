/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.PairOrthogonality
import Erdos522.Probability.LogMoments.RestrictedBilinear

/-!
# The matrix of restricted Fourier energy

The off-diagonal entries are the integrals of conjugate Fourier modes over a
set. Bilinear Khintchine and Hölder bound its Hilbert–Schmidt norm independently
of the number of coefficients.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Erdos522.LogMoments

/-- The off-diagonal part of the Gram matrix of the restricted Fourier modes. -/
def restrictedPairMatrix {N : ℕ} (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => if i = j then 0 else ∫ q in E, pairMode j i q ∂fourierMeasure N

@[simp] theorem restrictedPairMatrix_diag {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (i : Fin (N + 1)) :
    restrictedPairMatrix E i i = 0 := by simp [restrictedPairMatrix]

/-- Reversing an ordered pair conjugates the matrix entry. -/
theorem conjugate_restrictedPairMatrix {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (i j : Fin (N + 1)) :
    conj (restrictedPairMatrix E i j) = restrictedPairMatrix E j i := by
  by_cases hij : i = j
  · subst j; simp
  · simp only [restrictedPairMatrix, hij, Ne.symm hij, ite_false]
    rw [← integral_conj]
    simp only [conjugate_pairMode]

theorem restrictedPairMatrix_isHermitian {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    (restrictedPairMatrix E).IsHermitian := by
  ext i j
  exact conjugate_restrictedPairMatrix E j i

/-- Expanding a quadratic Fourier sum into its ordered-pair modes. -/
theorem randomBilinearFourier_eq_sum_pairMode {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (q : SignVector N × AddCircle (1 : ℝ)) :
    randomBilinearFourier A q =
      ∑ i, ∑ j, (if i = j then 0 else A i j) * pairMode i j q := by
  unfold randomBilinearFourier complexQuadraticSignSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ite_false, pairMode]
    ring

/-- The restricted integral of the matrix's own quadratic Fourier sum is its
    squared Hilbert–Schmidt norm. -/
theorem integral_randomBilinearFourier_restrictedPairMatrix {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    (∫ q in E, randomBilinearFourier (restrictedPairMatrix E) q ∂fourierMeasure N) =
      ((∑ i, ∑ j, ‖restrictedPairMatrix E i j‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [randomBilinearFourier_eq_sum_pairMode]
  have hint (i j : Fin (N + 1)) : Integrable
      (fun q => (if i = j then 0 else restrictedPairMatrix E i j) * pairMode i j q)
      ((fourierMeasure N).restrict E) :=
    ((integrable_pairMode i j).restrict).const_mul _
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hint i j))]
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  by_cases hij : i = j
  · subst j; simp
  · rw [ite_eq_right hij]
    have hij' : (∫ q in E, pairMode i j q ∂fourierMeasure N) =
        restrictedPairMatrix E j i := by simp [restrictedPairMatrix, Ne.symm hij]
    rw [hij', ← conjugate_restrictedPairMatrix E i j, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]

/-- The Hilbert–Schmidt norm of restricted off-diagonal Fourier energy has
    measure exponent arbitrarily close to one. -/
theorem restrictedPairMatrix_hilbertSchmidt_le {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt (∑ i, ∑ j, ‖restrictedPairMatrix E i j‖ ^ 2) ≤
      (16 * Real.exp 2 * (m : ℝ)) *
        (fourierMeasure N).real E ^ (1 - 1 / (2 * (m : ℝ))) := by
  let S : ℝ := ∑ i, ∑ j, ‖restrictedPairMatrix E i j‖ ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have henergy : ∑ i, ∑ j,
      (if i = j then 0 else ‖restrictedPairMatrix E i j‖ ^ 2) = S := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij]
  by_cases hS0 : S = 0
  · change Real.sqrt S ≤ _
    rw [hS0, Real.sqrt_zero]
    positivity
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  have h := integral_norm_randomBilinearFourier_restrict_le
    (restrictedPairMatrix E) hSpos (by rw [henergy]) m hm E
  have hlower : S ≤ ∫ q in E,
      ‖randomBilinearFourier (restrictedPairMatrix E) q‖ ∂fourierMeasure N := by
    have hn := norm_integral_le_integral_norm
      (μ := (fourierMeasure N).restrict E) (randomBilinearFourier (restrictedPairMatrix E))
    rw [integral_randomBilinearFourier_restrictedPairMatrix, Complex.norm_real,
      Real.norm_of_nonneg hS] at hn
    exact hn
  have hsq := Real.sq_sqrt hS
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
  change Real.sqrt S ≤ _
  nlinarith [hlower.trans h]

end Erdos522.LogMoments
