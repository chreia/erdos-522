/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.FiniteFourier
import Erdos522.Basic.PolynomialPrefixes
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Polynomial prefixes with Rademacher coefficients

The finite sign polynomial is the restriction of one coefficient sequence.
Evaluation and radial differentiation keep the degree and normalization explicit.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Erdos522
open LogMoments

/-- The degree-indexed polynomial with the finite vector of fair coefficient signs. -/
def rademacherPolynomial (N : ℕ) (ω : SignVector N) : ℂ[X] :=
  signedPolynomial (fun _ => 1) ω

/-- Evaluation of the finite sign polynomial is the coefficient sum. -/
theorem rademacherPolynomial_eval (N : ℕ) (ω : SignVector N) (w : ℂ) :
    (rademacherPolynomial N ω).eval w = ∑ k, sign (ω k) * w ^ k.val := by
  simp only [rademacherPolynomial, signedPolynomial, eval_finsetSum, eval_monomial, mul_one]

/-- Multiplying the derivative by the evaluation point restores the original powers. -/
theorem rademacherPolynomial_radial_derivative (N : ℕ) (ω : SignVector N) (w : ℂ) :
    w * (rademacherPolynomial N ω).derivative.eval w =
      ∑ k, (k.val : ℂ) * sign (ω k) * w ^ k.val := by
  simp only [rademacherPolynomial, signedPolynomial, derivative_sum, derivative_monomial,
    mul_one, eval_finsetSum, eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases hk : k.val with
  | zero => simp
  | succ j => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- Restricting one infinite coin sequence gives exactly its polynomial prefix. -/
theorem rademacherPolynomial_eq_prefix (ε : ℕ → Bool) (N : ℕ) :
    rademacherPolynomial N (fun k => ε k.val) =
      polynomialPrefix (fun k => sign (ε k)) (fun _ => 1) N := by
  unfold rademacherPolynomial signedPolynomial polynomialPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [C_mul_X_pow_eq_monomial]

/-- Every prefix of the fixed sign sequence has its stated degree. -/
theorem rademacherPolynomial_prefix_natDegree (ε : ℕ → Bool) (N : ℕ) :
    (rademacherPolynomial N (fun k => ε k.val)).natDegree = N := by
  rw [rademacherPolynomial_eq_prefix]
  exact polynomialPrefix_natDegree _ _ N (by simp)


end Erdos522
