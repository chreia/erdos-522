/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.ZeroCount
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators

/-! Successive polynomial prefixes of one weighted coefficient sequence. -/

noncomputable section

namespace Erdos522

open Polynomial

/-- The degree-`N` prefix of a fixed coefficient sequence with deterministic weights. -/
def polynomialPrefix (ξ c : ℕ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N + 1), C (ξ k * c k) * X ^ k

/-- The coefficients appended between two prefixes. -/
def polynomialTail (ξ c : ℕ → ℂ) (N n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.Ico (N + 1) (n + 1), C (ξ k * c k) * X ^ k

@[simp] theorem polynomialPrefix_coeff (ξ c : ℕ → ℂ) (N k : ℕ) :
    (polynomialPrefix ξ c N).coeff k = if k ≤ N then ξ k * c k else 0 := by
  classical
  unfold polynomialPrefix
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

@[simp] theorem polynomialPrefix_eval (ξ c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (polynomialPrefix ξ c N).eval z =
      ∑ k ∈ Finset.range (N + 1), ξ k * c k * z ^ k := by
  unfold polynomialPrefix
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

theorem polynomialPrefix_succ (ξ c : ℕ → ℂ) (N : ℕ) :
    polynomialPrefix ξ c (N + 1) =
      polynomialPrefix ξ c N + C (ξ (N + 1) * c (N + 1)) * X ^ (N + 1) := by
  simp only [polynomialPrefix, Finset.sum_range_succ]

theorem polynomialPrefix_eq_add_tail (ξ c : ℕ → ℂ) {N n : ℕ} (h : N ≤ n) :
    polynomialPrefix ξ c n = polynomialPrefix ξ c N + polynomialTail ξ c N n := by
  unfold polynomialPrefix polynomialTail
  exact (Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right h 1)).symm

theorem polynomialPrefix_natDegree_le (ξ c : ℕ → ℂ) (N : ℕ) :
    (polynomialPrefix ξ c N).natDegree ≤ N := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [not_le_of_gt hk]

theorem polynomialPrefix_natDegree (ξ c : ℕ → ℂ) (N : ℕ)
    (h : ξ N * c N ≠ 0) : (polynomialPrefix ξ c N).natDegree = N := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (polynomialPrefix_natDegree_le ξ c N)
  simpa using h

theorem polynomialPrefix_ne_zero (ξ c : ℕ → ℂ) (N : ℕ)
    (h : ξ 0 * c 0 ≠ 0) : polynomialPrefix ξ c N ≠ 0 := by
  intro hp
  have hz := congrArg (fun P : Polynomial ℂ ↦ P.coeff 0) hp
  exact h (by simpa using hz)

theorem closedZeroCount_prefix_le (ξ c : ℕ → ℂ) (N : ℕ) (r : ℝ) :
    closedZeroCount (polynomialPrefix ξ c N) r ≤ N :=
  (zeroCountIn_le_natDegree _ _).trans (polynomialPrefix_natDegree_le ξ c N)

end Erdos522
