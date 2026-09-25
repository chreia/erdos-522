/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.RestrictedPairMatrix

/-!
# Restricted energy and the finite Hermitian matrix

The diagonal of the restricted Gram matrix is the event measure. Its off-diagonal
part acts on the original coefficient vector, with the native complex inner product.
-/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace Erdos522.LogMoments

@[simp] lemma pairMode_self {N : ℕ} (i : Fin (N + 1))
    (q : SignVector N × AddCircle (1 : ℝ)) : pairMode i i q = 1 := by
  have hs : sign (q.1 i) * sign (q.1 i) = 1 := by
    cases q.1 i <;> simp [sign]
  simp only [pairMode, sub_self, fourier_zero, hs, mul_one]

/-- Squared modulus expands into ordered pair modes with the original coefficients. -/
theorem norm_sq_randomFourier_eq_sum_pairMode {N : ℕ}
    (a : Fin (N + 1) → ℂ) (q : SignVector N × AddCircle (1 : ℝ)) :
    Complex.ofReal (‖randomFourier a q‖ ^ 2) =
      ∑ i, ∑ j, a i * conj (a j) * pairMode i j q := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [randomFourier, fourierPolynomial_eq_sum, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : conj (sign (q.1 j)) = sign (q.1 j) := by cases q.1 j <;> simp [sign]
  simp only [map_mul, hs, pairMode, sub_eq_add_neg, fourier_add, fourier_neg]
  ring

lemma integral_pairMode_eq_diagonal_add_matrix {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (i j : Fin (N + 1)) :
    (∫ q in E, pairMode i j q ∂fourierMeasure N) =
      (if i = j then ((fourierMeasure N).real E : ℂ) else 0) +
        restrictedPairMatrix E j i := by
  by_cases hij : i = j
  · subst j
    simp [integral_const]
  · simp [restrictedPairMatrix, hij, Ne.symm hij]

/-- Coordinate expansion of the native complex quadratic form. -/
lemma inner_toEuclideanLin_eq_sum {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (a : Fin (N + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 a) (Matrix.toEuclideanLin A (WithLp.toLp 2 a)) =
      ∑ i, ∑ j, a i * conj (a j) * A j i := by
  change inner ℂ (WithLp.toLp 2 a) (WithLp.toLp 2 (A *ᵥ a)) = _
  rw [PiLp.inner_apply, Finset.sum_comm]
  simp only [RCLike.inner_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The restricted squared norm equals diagonal energy plus the exact Hermitian
quadratic form of the off-diagonal restricted matrix. -/
theorem integral_norm_sq_randomFourier_eq_matrix {N : ℕ}
    (a : Fin (N + 1) → ℂ) (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) =
      (fourierMeasure N).real E * (∑ i, ‖a i‖ ^ 2) +
        (inner ℂ (WithLp.toLp 2 a)
          (Matrix.toEuclideanLin (restrictedPairMatrix E) (WithLp.toLp 2 a))).re := by
  have hcomplex : Complex.ofReal (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) =
      Complex.ofReal ((fourierMeasure N).real E * (∑ i, ‖a i‖ ^ 2)) +
        inner ℂ (WithLp.toLp 2 a)
          (Matrix.toEuclideanLin (restrictedPairMatrix E) (WithLp.toLp 2 a)) := by
    rw [← integral_complex_ofReal]
    simp_rw [norm_sq_randomFourier_eq_sum_pairMode]
    have hint (i j : Fin (N + 1)) : Integrable
        (fun q => a i * conj (a j) * pairMode i j q) ((fourierMeasure N).restrict E) :=
      ((integrable_pairMode i j).restrict).const_mul _
    rw [integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => hint i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul,
      integral_pairMode_eq_diagonal_add_matrix, mul_add, Finset.sum_add_distrib]
    rw [inner_toEuclideanLin_eq_sum]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.ofReal_re, Complex.add_re] using hreal

end Erdos522.LogMoments
