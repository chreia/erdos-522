/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Finite-dimensional spectral truncation

A self-adjoint operator with bounded Hilbert--Schmidt energy has only a small
subspace of eigenvalues below a fixed negative threshold. Its quadratic form
is bounded below on the orthogonal complement of that subspace.
-/

noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Erdos522

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hilbert--Schmidt energy of a self-adjoint operator does not depend on the
    orthonormal basis used to compute it. -/
theorem sum_sq_norm_apply_orthonormalBasis_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (e : OrthonormalBasis κ ℂ E)
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    (∑ i, ‖T (b i)‖ ^ 2) = ∑ j, ‖T (e j)‖ ^ 2 := by
  calc
    _ = ∑ i, ∑ j, ‖⟪e j, T (b i)⟫‖ ^ 2 := by
      simp only [e.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪T (e j), b i⟫‖ ^ 2 := by
      have hsym (i : ι) (j : κ) : ⟪e j, T (b i)⟫ = ⟪T (e j), b i⟫ :=
        (hT (e j) (b i)).symm
      simp_rw [hsym]
      exact Finset.sum_comm
    _ = _ := by simp only [b.sum_sq_norm_inner_left]

/-- In an orthonormal eigenbasis, the quadratic form is the weighted coordinate energy. -/
theorem re_inner_eq_sum_eigenvalues
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (T : E →ₗ[ℂ] E) (eigenvalue : ι → ℝ)
    (heigen : ∀ i, T (b i) = (eigenvalue i : ℂ) • b i) (x : E) :
    (⟪x, T x⟫).re = ∑ i, eigenvalue i * ‖⟪b i, x⟫‖ ^ 2 := by
  nth_rw 2 [← b.sum_repr' x]
  simp only [map_sum, map_smul, heigen, inner_sum, inner_smul_right, smul_smul,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← inner_conj_symm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- A bound on the sum of squared eigenvalues bounds the number below `-t`. -/
theorem card_negative_eigenvalues_le {ι : Type*} [Fintype ι]
    (eigenvalue : ι → ℝ) {t H : ℝ} (ht : 0 < t)
    (hH : ∑ i, (eigenvalue i) ^ 2 ≤ H) :
    ((Finset.univ.filter (fun i => eigenvalue i < -t)).card : ℝ) ≤ H / t ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => eigenvalue i < -t), t ^ 2 := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => eigenvalue i < -t), (eigenvalue i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      nlinarith
    _ ≤ ∑ i, (eigenvalue i) ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ H := hH

/-- Removing the negative eigenspaces below `-t` loses at most `H/t²` dimensions. -/
theorem exists_subspace_quadratic_lower_bound
    [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    {t H : ℝ} (ht : 0 < t) (hH : ∑ i, ‖T (b i)‖ ^ 2 ≤ H) :
    ∃ V : Submodule ℂ E, (Module.finrank ℂ V : ℝ) ≤ H / t ^ 2 ∧
      ∀ x ∈ Vᗮ, -t * ‖x‖ ^ 2 ≤ (⟪x, T x⟫).re := by
  classical
  let d := Module.finrank ℂ E
  let e := hT.eigenvectorBasis (n := d) rfl
  let v := hT.eigenvalues (n := d) rfl
  let bad : Finset (Fin d) := Finset.univ.filter (fun i => v i < -t)
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range (fun i : bad => e i.val))
  have heigen (i : Fin d) : T (e i) = (v i : ℂ) • e i := hT.apply_eigenvectorBasis rfl i
  have heH : ∑ i, (v i) ^ 2 ≤ H := by
    have hs := (sum_sq_norm_apply_orthonormalBasis_eq b e T hT).symm.le.trans hH
    simpa only [heigen, norm_smul, Complex.norm_real, e.orthonormal.norm_eq_one,
      mul_one, Real.norm_eq_abs, sq_abs] using hs
  have hdim : Module.finrank ℂ V ≤ bad.card := by
    simpa only [V, Set.finrank, Fintype.card_coe] using
      (finrank_range_le_card (R := ℂ) (fun i : bad => e i.val))
  have hdimr : (Module.finrank ℂ V : ℝ) ≤ (bad.card : ℝ) := by exact_mod_cast hdim
  refine ⟨V, hdimr.trans (card_negative_eigenvalues_le v ht heH), ?_⟩
  intro x hx
  rw [re_inner_eq_sum_eigenvalues e T v heigen x, ← e.sum_sq_norm_inner_right x,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ bad
  · have hmem : e i ∈ V := Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    have hz := V.inner_right_of_mem_orthogonal hmem hx
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact le_rfl
  · have hvi : -t ≤ v i := by simpa only [bad, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt] using hi
    exact mul_le_mul_of_nonneg_right hvi (sq_nonneg _)

/-- A positive scalar part dominates the operator off a subspace of controlled dimension. -/
theorem exists_subspace_shift_coercive
    [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    {δ H : ℝ} (hδ : 0 < δ) (hH : ∑ i, ‖T (b i)‖ ^ 2 ≤ H) :
    ∃ V : Submodule ℂ E, (Module.finrank ℂ V : ℝ) ≤ 4 * H / δ ^ 2 ∧
      ∀ x ∈ Vᗮ, (δ / 2) * ‖x‖ ^ 2 ≤ δ * ‖x‖ ^ 2 + (⟪x, T x⟫).re := by
  obtain ⟨V, hdim, hform⟩ := exists_subspace_quadratic_lower_bound b T hT
    (show 0 < δ / 2 by positivity) hH
  refine ⟨V, ?_, ?_⟩
  · convert hdim using 1
    field_simp
    ring
  · intro x hx
    have h := hform x hx
    linarith

/-- The Hilbert--Schmidt energy of a matrix is the sum of squared entry norms. -/
theorem sum_sq_norm_toEuclideanLin_basisFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (∑ i, ‖A.toEuclideanLin (EuclideanSpace.basisFun ι ℂ i)‖ ^ 2) =
      ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [EuclideanSpace.basisFun_apply, Matrix.toLpLin_apply, PiLp.ofLp_single,
    Matrix.mulVec_single_one, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_comm

/-- A Hermitian matrix with small entry energy is coercive after adding a positive scalar,
    outside a subspace of explicitly controlled dimension. -/
theorem exists_subspace_matrix_shift_coercive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {δ H : ℝ} (hδ : 0 < δ)
    (hH : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ H) :
    ∃ V : Submodule ℂ (EuclideanSpace ℂ ι), (Module.finrank ℂ V : ℝ) ≤ 4 * H / δ ^ 2 ∧
      ∀ x ∈ Vᗮ, (δ / 2) * ‖x‖ ^ 2 ≤
        δ * ‖x‖ ^ 2 + (⟪x, A.toEuclideanLin x⟫).re := by
  apply exists_subspace_shift_coercive (EuclideanSpace.basisFun ι ℂ)
    A.toEuclideanLin (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) hδ
  rwa [sum_sq_norm_toEuclideanLin_basisFun]

end Erdos522
