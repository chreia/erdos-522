/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Finite moment matrices for polynomial values and derivatives

The normalized moments of the grid `k/N`, for `0 ≤ k ≤ N`, give the
nonoscillatory covariance matrix of a polynomial and its scaled derivative.
Their exact formulas imply a uniform quadratic-form lower bound.
-/

noncomputable section
open scoped BigOperators Matrix
namespace Erdos522

/-- The normalized `j`th moment of the polynomial index grid. -/
def indexMoment (N j : ℕ) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1), ((k : ℝ) / (N : ℝ)) ^ j

/-- The two-dimensional moment matrix of the affine functions `1` and `k/N`. -/
def indexMomentMatrix (N : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![indexMoment N 0, indexMoment N 1; indexMoment N 1, indexMoment N 2]

theorem sum_index (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (k : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_index_sq (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ 2) =
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem indexMoment_zero (N : ℕ) : indexMoment N 0 = ((N : ℝ) + 1) / N := by
  simp [indexMoment, div_eq_mul_inv, mul_comm]

theorem indexMoment_one (N : ℕ) (hN : 0 < N) :
    indexMoment N 1 = ((N : ℝ) + 1) / (2 * N) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [indexMoment, pow_one]
  rw [← Finset.sum_div, sum_index]
  field_simp

theorem indexMoment_two (N : ℕ) (hN : 0 < N) :
    indexMoment N 2 = ((N : ℝ) + 1) * (2 * N + 1) / (6 * (N : ℝ) ^ 2) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [indexMoment, div_pow]
  rw [← Finset.sum_div, sum_index_sq]
  field_simp

/-- The exact determinant of the finite moment matrix. -/
theorem indexMomentMatrix_det (N : ℕ) (hN : 0 < N) :
    (indexMomentMatrix N).det = ((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 2) /
      (12 * (N : ℝ) ^ 3) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [indexMomentMatrix, Matrix.det_fin_two_of, indexMoment_zero,
    indexMoment_one N hN, indexMoment_two N hN]
  field_simp
  ring

/-- The exact trace of the finite moment matrix. -/
theorem indexMomentMatrix_trace (N : ℕ) (hN : 0 < N) :
    (indexMomentMatrix N).trace = ((N : ℝ) + 1) * (8 * N + 1) /
      (6 * (N : ℝ) ^ 2) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [indexMomentMatrix, Matrix.trace_fin_two_of, indexMoment_zero,
    indexMoment_two N hN]
  field_simp
  ring

/-- The determinant-to-trace ratio is an explicit rational function of the degree. -/
theorem indexMomentMatrix_det_div_trace (N : ℕ) (hN : 0 < N) :
    (indexMomentMatrix N).det / (indexMomentMatrix N).trace =
      ((N : ℝ) + 1) * ((N : ℝ) + 2) / (2 * N * (8 * N + 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp : (N : ℝ) + 1 ≠ 0 := by positivity
  have hq : 8 * (N : ℝ) + 1 ≠ 0 := by positivity
  rw [indexMomentMatrix_det N hN, indexMomentMatrix_trace N hN]
  field_simp
  ring

/-- The finite moment matrix has determinant-to-trace ratio at least `1/16`. -/
theorem indexMomentMatrix_det_div_trace_lower (N : ℕ) (hN : 0 < N) :
    (1 : ℝ) / 16 ≤ (indexMomentMatrix N).det / (indexMomentMatrix N).trace := by
  rw [indexMomentMatrix_det_div_trace N hN]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N * (8 * N + 1))).mpr
  nlinarith

/-- The principal-minor test for a real symmetric two-dimensional quadratic form. -/
theorem quadratic_nonneg_of_minor {a b c : ℝ} (ha : 0 < a)
    (hdet : 0 ≤ a * c - b ^ 2) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  have hp : 0 ≤ (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by positivity
  have he : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) =
      (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by ring
  nlinarith

/-- Every affine coefficient vector has uniformly positive grid energy. -/
theorem indexMoment_quadratic_lower (N : ℕ) (hN : 0 < N) (x y : ℝ) :
    (x ^ 2 + y ^ 2) / 16 ≤
      indexMoment N 0 * x ^ 2 + 2 * indexMoment N 1 * x * y + indexMoment N 2 * y ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := hn.ne'
  have ha : 0 < indexMoment N 0 - 1 / 16 := by
    rw [indexMoment_zero]
    have h : (1 : ℝ) ≤ ((N : ℝ) + 1) / N := (le_div_iff₀ hn).mpr (by linarith)
    linarith
  have he : (indexMoment N 0 - 1 / 16) * (indexMoment N 2 - 1 / 16) -
      (indexMoment N 1) ^ 2 =
      (3 * (N : ℝ) ^ 3 + 184 * (N : ℝ) ^ 2 + 312 * N + 128) / (768 * (N : ℝ) ^ 3) := by
    rw [indexMoment_zero, indexMoment_one N hN, indexMoment_two N hN]
    field_simp
    ring
  have hdet : 0 ≤ (indexMoment N 0 - 1 / 16) * (indexMoment N 2 - 1 / 16) -
      (indexMoment N 1) ^ 2 := by rw [he]; positivity
  have h := quadratic_nonneg_of_minor ha hdet x y
  nlinarith

/-- The quadratic form is the average squared affine function on the grid. -/
theorem indexMoment_quadratic_eq_sum (N : ℕ) (x y : ℝ) :
    indexMoment N 0 * x ^ 2 + 2 * indexMoment N 1 * x * y +
      indexMoment N 2 * y ^ 2 =
      (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
        (x + (k : ℝ) / N * y) ^ 2 := by
  simp only [indexMoment]
  simp_rw [show ∀ k : ℕ, (x + (k : ℝ) / N * y) ^ 2 =
      ((k : ℝ) / N) ^ 0 * x ^ 2 + 2 * ((k : ℝ) / N) ^ 1 * x * y +
        ((k : ℝ) / N) ^ 2 * y ^ 2 by intro k; ring]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- A lower bound on radial weights preserves the grid energy bound. -/
theorem weighted_index_energy_lower (N : ℕ) (hN : 0 < N) (w : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hw : ∀ k ≤ N, c ≤ w k) (x y : ℝ) :
    c * (x ^ 2 + y ^ 2) / 16 ≤
      (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
        w k * (x + (k : ℝ) / N * y) ^ 2 := by
  calc
    c * (x ^ 2 + y ^ 2) / 16 ≤
        c * (indexMoment N 0 * x ^ 2 + 2 * indexMoment N 1 * x * y +
          indexMoment N 2 * y ^ 2) := by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left (indexMoment_quadratic_lower N hN x y) hc
    _ = (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
        c * (x + (k : ℝ) / N * y) ^ 2 := by
      rw [indexMoment_quadratic_eq_sum, ← Finset.mul_sum]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hw k (by simpa using hk)) (sq_nonneg _)

end Erdos522
