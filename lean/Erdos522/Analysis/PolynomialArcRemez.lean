/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Polynomial bounds from a circular arc

Lagrange interpolation converts separation of sampling points into a quantitative
bound for a polynomial on the unit circle.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Erdos522

/-- Lagrange interpolation with every distance factor retained explicitly. -/
theorem polynomial_norm_le_interpolation_sum {ι : Type*} [DecidableEq ι]
    (P : Polynomial ℂ) (s : Finset ι) (v : ι → ℂ)
    (hv : Set.InjOn v s) (hP : P.degree < s.card) (z : ℂ) :
    ‖P.eval z‖ ≤ ∑ i ∈ s, ‖P.eval (v i)‖ *
      ∏ j ∈ s.erase i, (‖z - v j‖ / ‖v i - v j‖) := by
  have hinterp := Lagrange.eq_interpolate hv hP
  conv_lhs => rw [hinterp, Lagrange.interpolate_apply]
  simp only [eval_finsetSum, eval_mul, eval_C]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simp only [norm_mul, Lagrange.basis, eval_prod, Lagrange.basisDivisor,
    eval_mul, eval_C, eval_sub, eval_X, norm_prod, norm_mul, norm_inv,
    div_eq_mul_inv, mul_comm]
  exact le_rfl

/-- Interpolation on the closed unit disk when all sampled values are small. -/
theorem polynomial_norm_le_separated_interpolation {ι : Type*} [DecidableEq ι]
    (P : Polynomial ℂ) (s : Finset ι) (v : ι → ℂ)
    (hv : Set.InjOn v s) (hP : P.degree < s.card) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hvnorm : ∀ i ∈ s, ‖v i‖ ≤ 1) {ε : ℝ}
    (hε : ∀ i ∈ s, ‖P.eval (v i)‖ ≤ ε) :
    ‖P.eval z‖ ≤ ε * ∑ i ∈ s, ∏ j ∈ s.erase i, (2 / ‖v i - v j‖) := by
  apply (polynomial_norm_le_interpolation_sum P s v hv hP z).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul (hε i hi) _ (by positivity)
    ((norm_nonneg _).trans (hε i hi))
  apply Finset.prod_le_prod₀
  · intro j hj
    positivity
  · intro j hj
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    have h := (norm_sub_le z (v j)).trans (add_le_add hz (hvnorm j (Finset.mem_of_mem_erase hj)))
    norm_num at h ⊢
    exact h


/-- The product of the distances from one integer node to all the other nodes. -/
theorem prod_integer_node_distances (n i : ℕ) (hi : i ≤ n) :
    (∏ j ∈ (Finset.range (n + 1)).erase i, |(i : ℝ) - j|) =
      (i.factorial : ℝ) * ((n - i).factorial : ℝ) := by
  induction n generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst i
    simp
  | succ n ih =>
    by_cases hi' : i = n + 1
    · subst i
      rw [Finset.range_add_one, Finset.erase_insert (by simp)]
      have habs : ∀ j ∈ Finset.range (n + 1), |((n + 1 : ℕ) : ℝ) - j| =
          ((n + 1 : ℕ) : ℝ) - j := by
        intro j hj
        apply abs_of_nonneg
        exact sub_nonneg.mpr (by exact_mod_cast (Finset.mem_range.mp hj).le)
      simp_rw [Finset.prod_congr rfl habs, Finset.prod_range_natCast_sub,
        ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
      simp
    · have hin : i ≤ n := by omega
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm hi'),
        Finset.prod_insert (by simp), ih i hin]
      have hsub : |(i : ℝ) - ((n + 1 : ℕ) : ℝ)| = (n + 1 - i : ℕ) := by
        rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (show i ≤ n + 1 by omega))), neg_sub,
          Nat.cast_sub (by omega)]
      rw [hsub]
      have hsucc : n + 1 - i = (n - i) + 1 := by omega
      rw [hsucc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring


/-- Summing the reciprocal integer-node separation products gives a binomial identity. -/
theorem sum_inv_integer_node_distances (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      ((i.factorial : ℝ) * ((n - i).factorial : ℝ))⁻¹) = 2 ^ n / (n.factorial : ℝ) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ((i.factorial : ℝ) * ((n - i).factorial : ℝ))⁻¹ =
        (n.choose i : ℝ) / (n.factorial : ℝ) := by
    rw [Nat.cast_choose ℝ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    field_simp
  simp_rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hsum]

/-- The elementary factorial lower bound needed to remove the degree from the constant. -/
theorem pow_div_exp_le_factorial (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.two_le_pi]
  exact (le_mul_of_one_le_left (by positivity) hroot).trans (Stirling.le_factorial_stirling n)

/-- Equally spaced separation of the nodes yields an explicit degree-independent constant. -/
theorem polynomial_norm_le_of_node_separation (P : Polynomial ℂ) (n : ℕ)
    (v : ℕ → ℂ) (hv : Set.InjOn v (Finset.range (n + 1)))
    (hP : P.degree < n + 1) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hvnorm : ∀ i ≤ n, ‖v i‖ ≤ 1) {ε d : ℝ} (hd : 0 < d)
    (hε : ∀ i ≤ n, ‖P.eval (v i)‖ ≤ ε)
    (hsep : ∀ i ≤ n, ∀ j ≤ n, d * |(i : ℝ) - j| ≤ ‖v i - v j‖) :
    ‖P.eval z‖ ≤ ε * (4 / d) ^ n / (n.factorial : ℝ) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0 (Nat.zero_le _))
  have hbase := polynomial_norm_le_separated_interpolation P (Finset.range (n + 1)) v hv
    (by simpa using hP) hz (fun i hi => hvnorm i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    (fun i hi => hε i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  apply hbase.trans
  have hprod (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      (∏ j ∈ (Finset.range (n + 1)).erase i, 2 / ‖v i - v j‖) ≤
        (2 / d) ^ n * ((i.factorial : ℝ) * ((n - i).factorial : ℝ))⁻¹ := by
    calc
      _ ≤ ∏ j ∈ (Finset.range (n + 1)).erase i, 2 / (d * |(i : ℝ) - j|) := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro j hj
        have hij : (i : ℝ) - j ≠ 0 := by
          rw [sub_ne_zero]
          exact_mod_cast (Finset.ne_of_mem_erase hj).symm
        exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hd (abs_pos.mpr hij))
          (hsep i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) j
            (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))))
      _ = _ := by
        simp_rw [div_mul_eq_div_div, Finset.prod_div_distrib]
        simp only [Finset.prod_const, Finset.card_erase_of_mem hi, Finset.card_range,
          Nat.add_sub_cancel, prod_integer_node_distances n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), div_eq_mul_inv, mul_pow, inv_pow]
  calc
    ε * ∑ i ∈ Finset.range (n + 1), ∏ j ∈ (Finset.range (n + 1)).erase i, 2 / ‖v i - v j‖
        ≤ ε * ∑ i ∈ Finset.range (n + 1),
          (2 / d) ^ n * ((i.factorial : ℝ) * ((n - i).factorial : ℝ))⁻¹ := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hprod) hε0
    _ = ε * (4 / d) ^ n / (n.factorial : ℝ) := by
      rw [← Finset.mul_sum, sum_inv_integer_node_distances]
      rw [div_pow, div_pow, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
      ring


/-- The unit-circle point of angular coordinate `θ`, in radians. -/
def unitCirclePoint (θ : ℝ) : ℂ := Complex.exp (Complex.I * θ)

@[simp] theorem norm_unitCirclePoint (θ : ℝ) : ‖unitCirclePoint θ‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal θ

/-- Chord length controls angular separation on a semicircle. -/
theorem angular_separation_le_chord {u v : ℝ} (huv : |u - v| ≤ Real.pi) :
    (2 / Real.pi) * |u - v| ≤ ‖unitCirclePoint u - unitCirclePoint v‖ := by
  have hnorm : ‖unitCirclePoint u - unitCirclePoint v‖ =
      ‖Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1‖ := by
    have heq : unitCirclePoint u - unitCirclePoint v =
        (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) * unitCirclePoint v := by
      simp only [unitCirclePoint, Complex.ofReal_sub, mul_sub, Complex.exp_sub,
        sub_mul, one_mul]
      rw [div_mul_cancel₀ _ (Complex.exp_ne_zero _)]
    rw [heq, norm_mul, norm_unitCirclePoint, mul_one]
  rw [hnorm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := Real.mul_abs_le_abs_sin (x := (u - v) / 2) (by simpa [abs_div] using
    (div_le_div_of_nonneg_right huv (by norm_num : (0 : ℝ) ≤ 2)))
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  nlinarith

/-- Sampling points on the first half of an arc of normalized length `ℓ`. -/
def arcInterpolationNode (θ ℓ : ℝ) (n i : ℕ) : ℂ :=
  unitCirclePoint (θ + Real.pi * ℓ * i / n)

/-- Consecutive interpolation points are separated in proportion to their index distance. -/
theorem arcInterpolationNode_separation {θ ℓ : ℝ} {n : ℕ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hn : 0 < n)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    (2 * ℓ / n) * |(i : ℝ) - j| ≤
      ‖arcInterpolationNode θ ℓ n i - arcInterpolationNode θ ℓ n j‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hdiff : |(i : ℝ) - j| ≤ n := abs_le.mpr ⟨by linarith, by linarith⟩
  have hangle : |(θ + Real.pi * ℓ * i / n) - (θ + Real.pi * ℓ * j / n)| =
      Real.pi * ℓ / n * |(i : ℝ) - j| := by
    have heq : (θ + Real.pi * ℓ * i / n) - (θ + Real.pi * ℓ * j / n) =
        (Real.pi * ℓ / n) * ((i : ℝ) - j) := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
  have h := angular_separation_le_chord (u := θ + Real.pi * ℓ * i / n)
    (v := θ + Real.pi * ℓ * j / n) (by
      rw [hangle]
      calc
        _ ≤ (Real.pi * ℓ / n) * n := mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = Real.pi * ℓ := div_mul_cancel₀ _ hn0.ne'
        _ ≤ Real.pi := by nlinarith [Real.pi_pos])
  rw [hangle] at h
  convert h using 1 <;> try rfl
  field_simp


/-- Distinct indices give distinct interpolation nodes on the half arc. -/
theorem arcInterpolationNode_injOn {θ ℓ : ℝ} {n : ℕ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hn : 0 < n) :
    Set.InjOn (arcInterpolationNode θ ℓ n) (Finset.range (n + 1)) := by
  intro i hi j hj hij
  have h := arcInterpolationNode_separation (θ := θ) hℓ hℓ1 hn
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [hij, sub_self, norm_zero] at h
  have hd : 0 < 2 * ℓ / (n : ℝ) := by positivity
  have habs : |(i : ℝ) - j| = 0 := by
    have hnonpos : |(i : ℝ) - j| ≤ 0 := by nlinarith [abs_nonneg ((i : ℝ) - j)]
    exact le_antisymm hnonpos (abs_nonneg _)
  exact_mod_cast (sub_eq_zero.mp (abs_eq_zero.mp habs))

/-- A polynomial bounded on an arc is bounded on the whole closed unit disk.
The arc has normalized angular length `ℓ`, and the universal constant is `2 exp(1)`. -/
theorem polynomial_norm_le_of_arc (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {θ ℓ ε : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (harc : ∀ t ∈ Set.Icc θ (θ + 2 * Real.pi * ℓ), ‖P.eval (unitCirclePoint t)‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖P.eval z‖ ≤ ε * (2 * Real.exp 1 / ℓ) ^ n := by
  have hθ : θ ∈ Set.Icc θ (θ + 2 * Real.pi * ℓ) := ⟨le_rfl, le_add_of_nonneg_right (by positivity)⟩
  have hε0 := (norm_nonneg _).trans (harc θ hθ)
  by_cases hn : n = 0
  · subst n
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hP)
    have heq : P.eval z = P.eval (unitCirclePoint θ) := by rw [hconst]; simp
    simpa only [heq, pow_zero, mul_one] using harc θ hθ
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdegree : P.degree < (n : WithBot ℕ) + 1 := by
    exact lt_of_le_of_lt P.degree_le_natDegree (by exact_mod_cast (Nat.lt_succ_of_le hP))
  have hvalues (i : ℕ) (hi : i ≤ n) : ‖P.eval (arcInterpolationNode θ ℓ n i)‖ ≤ ε := by
    apply harc
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
      have hpart : Real.pi * ℓ * i / n ≤ Real.pi * ℓ := by
        apply (div_le_iff₀ hn0).mpr
        exact mul_le_mul_of_nonneg_left hin (by positivity)
      nlinarith [Real.pi_pos]
  have hraw := polynomial_norm_le_of_node_separation P n (arcInterpolationNode θ ℓ n)
    (arcInterpolationNode_injOn hℓ hℓ1 hnpos) hdegree hz
    (fun i _ => (norm_unitCirclePoint _).le) (by positivity : 0 < 2 * ℓ / (n : ℝ))
    hvalues (fun i hi j hj => arcInterpolationNode_separation hℓ hℓ1 hnpos hi hj)
  have hfactor : (4 / (2 * ℓ / (n : ℝ))) ^ n / (n.factorial : ℝ) ≤
      (2 * Real.exp 1 / ℓ) ^ n := by
    calc
      _ ≤ (4 / (2 * ℓ / (n : ℝ))) ^ n / (((n : ℝ) / Real.exp 1) ^ n) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_div_exp_le_factorial n)
      _ = _ := by
        rw [← div_pow]
        congr 1
        field_simp
        norm_num
  exact hraw.trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hfactor hε0)

/-- If a polynomial reaches modulus one on the unit circle, every arc of positive
normalized length `ℓ` has supremum at least `(ℓ / (2 exp(1)))^n`. -/
theorem polynomial_arc_lower_bound (P : Polynomial ℂ) {n : ℕ}
    (hP : P.natDegree ≤ n) {θ ℓ ε : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (harc : ∀ t ∈ Set.Icc θ (θ + 2 * Real.pi * ℓ), ‖P.eval (unitCirclePoint t)‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ = 1) (hlarge : 1 ≤ ‖P.eval z‖) :
    (ℓ / (2 * Real.exp 1)) ^ n ≤ ε := by
  have h := hlarge.trans (polynomial_norm_le_of_arc P hP hℓ hℓ1 harc hz.le)
  have hp : 0 < (2 * Real.exp 1 / ℓ) ^ n := by positivity
  have hdiv := (div_le_iff₀ hp).mpr h
  simpa only [one_div, ← inv_pow, inv_div] using hdiv

end Erdos522
