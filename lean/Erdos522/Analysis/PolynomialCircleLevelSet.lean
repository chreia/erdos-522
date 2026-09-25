/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial modulus level sets on the unit circle

Multiplication by a conjugate reciprocal polynomial converts a modulus level
condition into an algebraic equation of at most twice the original degree.
-/

noncomputable section

open Polynomial

namespace Erdos522

/-- An algebraic equation for a modulus level set on the unit circle. -/
def circleLevelPolynomial (P : Polynomial ℂ) (n : ℕ) (ε : ℝ) : Polynomial ℂ :=
  P * (P.map (starRingEnd ℂ)).reflect n - C ((ε : ℂ) ^ 2) * X ^ n

/-- The reflected conjugate polynomial is `z^n` times the conjugate value on the unit circle. -/
theorem eval_reflect_conjugate_on_circle (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {z : ℂ} (hz : ‖z‖ = 1) :
    ((P.map (starRingEnd ℂ)).reflect n).eval z = z ^ n * (starRingEnd ℂ) (P.eval z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (z⁻¹) n
    (P.map (starRingEnd ℂ)) (P.natDegree_map_le.trans hP)
  simp only [invOf_eq_inv, inv_inv, eval₂_id] at h
  have heval : (P.map (starRingEnd ℂ)).eval (z⁻¹) = (starRingEnd ℂ) (P.eval z) := by
    rw [Complex.inv_eq_conj hz, eval_map]
    exact Polynomial.eval₂_hom (starRingEnd ℂ) z
  rw [heval, inv_pow] at h
  have h' := congrArg (fun w : ℂ => w * z ^ n) h
  rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hz0), mul_one] at h'
  exact h'.trans (mul_comm _ _)

/-- The algebraic equation agrees with the squared-modulus equation on the unit circle. -/
theorem eval_circleLevelPolynomial (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) (ε : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    (circleLevelPolynomial P n ε).eval z = z ^ n * ((‖P.eval z‖ ^ 2 : ℝ) - ε ^ 2) := by
  rw [circleLevelPolynomial, eval_sub, eval_mul, eval_reflect_conjugate_on_circle P hP hz,
    eval_mul, eval_C, eval_pow, eval_X]
  have hconj : P.eval z * (starRingEnd ℂ) (P.eval z) = ((‖P.eval z‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' (P.eval z)
  calc
    _ = z ^ n * (P.eval z * (starRingEnd ℂ) (P.eval z) - (ε : ℂ) ^ 2) := by ring
    _ = _ := by rw [hconj]

/-- The level equation has degree at most twice the polynomial degree bound. -/
theorem natDegree_circleLevelPolynomial_le (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) (ε : ℝ) :
    (circleLevelPolynomial P n ε).natDegree ≤ 2 * n := by
  have hmap : (P.map (starRingEnd ℂ)).natDegree ≤ n := P.natDegree_map_le.trans hP
  have hreflect : ((P.map (starRingEnd ℂ)).reflect n).natDegree ≤ n := by
    exact Polynomial.natDegree_reflect_le.trans (max_le le_rfl hmap)
  unfold circleLevelPolynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (by omega)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp; omega)

/-- A unit-circle value different from the level prevents the algebraic equation from vanishing. -/
theorem circleLevelPolynomial_ne_zero (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : ‖z‖ = 1) (hne : ‖P.eval z‖ ≠ ε) :
    circleLevelPolynomial P n ε ≠ 0 := by
  intro hzero
  have h := eval_circleLevelPolynomial P hP ε hz
  rw [hzero, eval_zero] at h
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hsq : (‖P.eval z‖ ^ 2 : ℝ) - ε ^ 2 = 0 := by
    have hh := (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero n hz0)
    exact_mod_cast hh
  exact hne ((sq_eq_sq₀ (norm_nonneg _) hε).mp (sub_eq_zero.mp hsq))


/-- Points of the unit circle at which the polynomial has a prescribed modulus. -/
def polynomialCircleLevelSet (P : Polynomial ℂ) (ε : ℝ) : Set ℂ :=
  {z | ‖z‖ = 1 ∧ ‖P.eval z‖ = ε}

/-- A nonconstant modulus level is contained in the roots of the algebraic level equation. -/
theorem polynomialCircleLevelSet_subset_rootSet (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : ‖z‖ = 1) (hne : ‖P.eval z‖ ≠ ε) :
    polynomialCircleLevelSet P ε ⊆ (circleLevelPolynomial P n ε).rootSet ℂ := by
  intro w hw
  apply Polynomial.mem_rootSet.mpr
  refine ⟨circleLevelPolynomial_ne_zero P hP hε hz hne, ?_⟩
  change (circleLevelPolynomial P n ε).eval w = 0
  rw [eval_circleLevelPolynomial P hP ε hw.1, hw.2]
  simp

/-- A modulus level different from some unit-circle value has finitely many points. -/
theorem polynomialCircleLevelSet_finite (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : ‖z‖ = 1) (hne : ‖P.eval z‖ ≠ ε) :
    (polynomialCircleLevelSet P ε).Finite :=
  ((circleLevelPolynomial P n ε).rootSet_finite ℂ).subset
    (polynomialCircleLevelSet_subset_rootSet P hP hε hz hne)

/-- A nonconstant modulus level meets the unit circle at most `2n` times. -/
theorem polynomialCircleLevelSet_ncard_le (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : ‖z‖ = 1) (hne : ‖P.eval z‖ ≠ ε) :
    (polynomialCircleLevelSet P ε).ncard ≤ 2 * n := by
  calc
    _ ≤ ((circleLevelPolynomial P n ε).rootSet ℂ).ncard :=
      Set.ncard_le_ncard (polynomialCircleLevelSet_subset_rootSet P hP hε hz hne)
        ((circleLevelPolynomial P n ε).rootSet_finite ℂ)
    _ ≤ (circleLevelPolynomial P n ε).natDegree := Polynomial.ncard_rootSet_le _ ℂ
    _ ≤ 2 * n := natDegree_circleLevelPolynomial_le P hP ε

/-- Below a unit-circle value of modulus at least one, every nonnegative level
strictly less than one has at most twice the degree many points. -/
theorem polynomialCircleLevelSet_ncard_le_of_unit_value (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hlarge : 1 ≤ ‖P.eval z‖) :
    (polynomialCircleLevelSet P ε).Finite ∧ (polynomialCircleLevelSet P ε).ncard ≤ 2 * n := by
  have hne : ‖P.eval z‖ ≠ ε := (hε1.trans_le hlarge).ne'
  exact ⟨polynomialCircleLevelSet_finite P hP hε hz hne,
    polynomialCircleLevelSet_ncard_le P hP hε hz hne⟩

end Erdos522
