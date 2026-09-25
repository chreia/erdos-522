/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.PolynomialArcRemez
import Mathlib.Algebra.Order.Chebyshev

/-!
# Polynomial energy at separated points

Lagrange interpolation bounds a polynomial on the closed unit disk by its
values at separated nodes. Cauchy–Schwarz then gives a lower bound for the
sum of squared sample values whenever the polynomial reaches modulus one.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Erdos522

/-- Interpolation at `n + 1` separated points of the closed unit disk. -/
theorem polynomial_norm_le_separated_samples (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) (v : Fin (n + 1) → ℂ)
    (hv : ∀ i, ‖v i‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖v i - v j‖) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖P.eval z‖ ≤ (2 / δ) ^ n * ∑ i, ‖P.eval (v i)‖ := by
  classical
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin (n + 1))) := by
    intro i _ j _ hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, sub_self, norm_zero] at h
    exact (not_le_of_gt hδ) h
  have hdeg : P.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt P.degree_le_natDegree (by exact_mod_cast (Nat.lt_succ_of_le hP))
  apply (polynomial_norm_le_interpolation_sum P Finset.univ v hinj hdeg z).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_comm ((2 / δ) ^ n)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, (2 / δ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro j hj
      have hji := Finset.ne_of_mem_erase hj
      have hden : δ ≤ ‖v i - v j‖ := hsep i j hji.symm
      have hnum : ‖z - v j‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hv j])
      exact div_le_div₀ (by positivity) hnum hδ hden
    _ = (2 / δ) ^ n := by simp [div_pow]

/-- A polynomial reaching modulus one has a definite squared energy on separated nodes. -/
theorem polynomial_separated_energy_lower_bound (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) (v : Fin (n + 1) → ℂ)
    (hv : ∀ i, ‖v i‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖v i - v j‖) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hlarge : 1 ≤ ‖P.eval z‖) :
    (δ / 2) ^ (2 * n) / (n + 1 : ℝ) ≤ ∑ i, ‖P.eval (v i)‖ ^ 2 := by
  have h := hlarge.trans (polynomial_norm_le_separated_samples P hP v hv hδ hsep hz)
  have hfactor : 0 < (2 / δ) ^ n := by positivity
  have hsum : (δ / 2) ^ n ≤ ∑ i, ‖P.eval (v i)‖ := by
    have hd : 1 / (2 / δ) ^ n ≤ ∑ i, ‖P.eval (v i)‖ :=
      (div_le_iff₀ hfactor).mpr (by simpa only [mul_comm] using h)
    simpa only [one_div, ← inv_pow, inv_div] using hd
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (δ / 2) ^ n) hsum 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i : Fin (n + 1) => ‖P.eval (v i)‖)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hcs
  apply (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mpr
  have hpower : ((δ / 2) ^ n) ^ 2 = (δ / 2) ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  rw [hpower] at hsq
  nlinarith

end Erdos522
