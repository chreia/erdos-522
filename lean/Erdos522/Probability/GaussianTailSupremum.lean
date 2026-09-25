/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianTails
import Erdos522.Probability.TailSupremum

/-!
# Uniform appended-tail bounds for Gaussian polynomials

A shared Gaussian coefficient vector supplies all prefixes in a degree block.
Pointwise Gaussian tails, coefficient truncation, and an `N⁴` boundary grid
control the whole block simultaneously.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522
open TailSupremum

/-- Coefficients appended after degree `N`, truncated after `m` new coefficients. -/
def gaussianAppendedTailPolynomial (N M m : ℕ) (g : Fin (N + M + 1) → ℝ) : Polynomial ℂ :=
  ∑ k : Fin (N + M + 1), if N < k.val ∧ k.val ≤ N + m then
    monomial k.val ((g k : ℂ)) else 0

/-- Evaluation is a linear combination of the common Gaussian coefficient vector. -/
theorem gaussianAppendedTailPolynomial_eval (N M m : ℕ) (g : Fin (N + M + 1) → ℝ) (z : ℂ) :
    (gaussianAppendedTailPolynomial N M m g).eval z =
      complexGaussianSum (tailCoefficient N M m z) g := by
  classical
  simp only [gaussianAppendedTailPolynomial, eval_finsetSum, complexGaussianSum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : N < k.val ∧ k.val ≤ N + m <;> simp [tailCoefficient, hk]

/-- At two thirds of the block amplitude, one prefix at one point costs at most `4N⁻²⁵`. -/
theorem gaussian_appended_tail_point_tail {N M : ℕ} (hN : 2 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    (m : ℕ) {K : ℝ} (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ 1 + K / N) :
    (gaussianCoefficientMeasure (N + M + 1)).real {ω |
      2 * tailAmplitude N M K / 3 ≤ ‖(gaussianAppendedTailPolynomial N M m ω).eval z‖} ≤
      4 / (N : ℝ) ^ 25 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hV : 0 < (M : ℝ) * Real.exp (4 * K) := by positivity
  simp_rw [gaussianAppendedTailPolynomial_eval]
  apply (measure_norm_complexGaussianSum_ge_le_sharp (tailCoefficient N M m z) hV
    (annular_tail_energy_le (by omega) hM m hK hz)
    (by unfold tailAmplitude; positivity : 0 ≤ 2 * tailAmplitude N M K / 3)).trans
  have heq : (2 * tailAmplitude N M K / 3) ^ 2 / (4 * ((M : ℝ) * Real.exp (4 * K))) =
      25 * Real.log N := by
    unfold tailAmplitude
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hexp : Real.exp (2 * K) ^ 2 = Real.exp (4 * K) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hexp]
    field_simp
    ring
  rw [neg_div, heq, Real.exp_neg, show (25 : ℝ) = (25 : ℕ) by norm_num,
    Real.exp_nat_mul, Real.exp_log hN0, div_eq_mul_inv]


/-- Coefficient truncation controls the derivative of every partial tail. -/
theorem gaussian_tail_derivative_bound (N M m : ℕ) (g : Fin (N + M + 1) → ℝ)
    (hg : ∀ k, |g k| ≤ (N : ℝ))
    {B : ℝ} (hB : 1 ≤ B) {z : ℂ} (hz : ‖z‖ ≤ B) :
    ‖(gaussianAppendedTailPolynomial N M m g).derivative.eval z‖ ≤
      (N : ℝ) * M * (N + M : ℝ) * B ^ (N + M) := by
  classical
  simp only [gaussianAppendedTailPolynomial, derivative_sum, eval_finsetSum]
  calc
    _ ≤ ∑ k : Fin (N + M + 1),
      ‖(if N < k.val ∧ k.val ≤ N + m then monomial k.val (g k : ℂ) else 0).derivative.eval z‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k : Fin (N + M + 1), if N < k.val then
        (N : ℝ) * ((N + M : ℝ) * B ^ (N + M)) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : N < k.val ∧ k.val ≤ N + m
      · simp only [ite_eq_left hk, ite_eq_left hk.1, derivative_monomial, eval_monomial,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast, norm_pow]
        have hkN : (k.val : ℝ) ≤ N + M := by exact_mod_cast Nat.le_of_lt_succ k.isLt
        have hp := (pow_le_pow_left₀ (norm_nonneg _) hz (k.val - 1)).trans
          (pow_le_pow_right₀ hB (by omega : k.val - 1 ≤ N + M))
        calc
          |g k| * (k.val : ℝ) * ‖z‖ ^ (k.val - 1) ≤
            (N : ℝ) * (N + M : ℝ) * B ^ (N + M) := by gcongr; exact hg k
          _ = _ := by ring
      · simp only [ite_eq_right hk, derivative_zero, eval_zero, norm_zero]
        split_ifs <;> positivity
    _ = _ := by rw [sum_after_degree_const]; ring

/-- The annular derivative envelope on the coefficient-truncation event. -/
theorem gaussian_annular_tail_derivative_bound {N M : ℕ} (hN : 0 < N) (hM : M ≤ N)
    (m : ℕ) (g : Fin (N + M + 1) → ℝ) (hg : ∀ k, |g k| ≤ (N : ℝ))
    {K : ℝ} (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ 1 + K / N) :
    ‖(gaussianAppendedTailPolynomial N M m g).derivative.eval z‖ ≤
      2 * (N : ℝ) ^ 2 * M * Real.exp (2 * K) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 1 ≤ 1 + K / (N : ℝ) := le_add_of_nonneg_right (by positivity)
  have hp := block_radius_pow_le hN hM hK
  have hNM : (N + M : ℝ) ≤ 2 * N := by exact_mod_cast (show N + M ≤ 2 * N by omega)
  calc
    _ ≤ (N : ℝ) * M * (N + M : ℝ) * (1 + K / N) ^ (N + M) :=
      gaussian_tail_derivative_bound N M m g hg hB hz
    _ ≤ (N : ℝ) * M * (2 * N) * Real.exp (2 * K) := by gcongr
    _ = _ := by ring

/-- The `N⁴` grid retains the original interpolation error after truncation. -/
theorem gaussian_tail_grid_error_lt {N M : ℕ} (hN : 4 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    {K : ℝ} (hK : 0 ≤ K) (hKN : K ≤ (N : ℝ)) :
    (2 * (N : ℝ) ^ 2 * M * Real.exp (2 * K)) *
      (2 * Real.pi * (1 + K / N) / (N ^ 4 : ℕ)) < tailAmplitude N M K / 3 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (2 * (N : ℝ) ^ 2 * M * Real.exp (2 * K)) *
      (2 * Real.pi * (1 + K / N) / (N ^ 4 : ℕ)) =
      (2 * N * M * Real.exp (2 * K)) *
        (2 * Real.pi * (1 + K / N) / (N ^ 3 : ℕ)) := by
    push_cast
    field_simp
  rw [he]
  exact tail_grid_error_lt hN hM0 hM hK hKN

/-- One exceptional event controls every appended prefix and every point of the disk. -/
theorem gaussian_appended_tail_supremum (N M : ℕ) (hN : 4 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    {K : ℝ} (hK : 0 ≤ K) (hKN : K ≤ (N : ℝ)) :
    (gaussianCoefficientMeasure (N + M + 1)).real {g | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / N ∧ tailAmplitude N M K ≤
        ‖(gaussianAppendedTailPolynomial N M m g).eval z‖} ≤
      1 / (N : ℝ) ^ 10 + 2 * (N + M + 1) * Real.exp (-(N : ℝ) ^ 2 / 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : 0 < 1 + K / (N : ℝ) := by positivity
  have hJ : 0 < N ^ 4 := pow_pos (by omega) _
  let zgrid := polynomialBoundaryGrid (1 + K / (N : ℝ)) (N ^ 4)
  have hgrid (i : Fin (N ^ 4)) : ‖zgrid i‖ ≤ 1 + K / (N : ℝ) := by
    simp [zgrid, abs_of_pos hR]
  let E : Set (Fin (N + M + 1) → ℝ) := {g | ∃ k, (N : ℝ) < |g k|}
  let A : Set (Fin (N + M + 1) → ℝ) := ⋃ p : Fin (M + 1) × Fin (N ^ 4), {g |
    2 * tailAmplitude N M K / 3 ≤ ‖(gaussianAppendedTailPolynomial N M p.1.val g).eval (zgrid p.2)‖}
  have hsub : {g : Fin (N + M + 1) → ℝ | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / N ∧ tailAmplitude N M K ≤
        ‖(gaussianAppendedTailPolynomial N M m g).eval z‖} ⊆ A ∪ E := by
    intro g hg
    by_cases hgE : g ∈ E
    · exact Or.inr hgE
    left
    have hcoeff : ∀ k, |g k| ≤ (N : ℝ) := fun k => le_of_not_gt (fun hk => hgE ⟨k, hk⟩)
    obtain ⟨m, hm, z, hz, hlarge⟩ := hg
    by_contra h
    have hsmall : ∀ i, ‖(gaussianAppendedTailPolynomial N M m g).eval (zgrid i)‖ ≤
        2 * tailAmplitude N M K / 3 := by
      intro i
      exact (lt_of_not_ge (fun hi => h (Set.mem_iUnion.mpr ⟨(⟨m, by omega⟩, i), hi⟩))).le
    have hdisk := polynomial_disk_bound_of_boundary_grid (gaussianAppendedTailPolynomial N M m g)
      hR (by positivity : 0 ≤ 2 * (N : ℝ) ^ 2 * M * Real.exp (2 * K)) hJ
      (fun w hw => gaussian_annular_tail_derivative_bound (by omega) hM m g hcoeff hK hw) hsmall hz
    have herr := gaussian_tail_grid_error_lt hN hM0 hM hK hKN
    linarith
  have hA : (gaussianCoefficientMeasure (N + M + 1)).real A ≤ 1 / (N : ℝ) ^ 10 := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (M + 1) × Fin (N ^ 4))))
      (fun p _ => gaussian_appended_tail_point_tail (by omega) hM0 hM p.1.val hK (hgrid p.2))
    have hsum' : (∑ p : Fin (M + 1) × Fin (N ^ 4), (gaussianCoefficientMeasure (N + M + 1)).real
        {g | 2 * tailAmplitude N M K / 3 ≤
          ‖(gaussianAppendedTailPolynomial N M p.1.val g).eval (zgrid p.2)‖}) ≤
        ((M + 1 : ℝ) * (N : ℝ) ^ 4) * (4 / (N : ℝ) ^ 25) := by simpa using hsum
    apply ((measureReal_iUnion_fintype_le _).trans hsum').trans
    have hMN : (M + 1 : ℝ) ≤ 2 * N := by exact_mod_cast (show M + 1 ≤ 2 * N by omega)
    have hpow : (8 : ℝ) ≤ (N : ℝ) ^ 10 := by
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
      exact (by norm_num : (8 : ℝ) ≤ 2 ^ 10).trans (pow_le_pow_left₀ (by norm_num) hN2 _)
    calc
      _ ≤ ((2 * N) * (N : ℝ) ^ 4) * (4 / (N : ℝ) ^ 25) := by gcongr
      _ = (8 / (N : ℝ) ^ 10) * (1 / (N : ℝ) ^ 10) := by field_simp; ring
      _ ≤ 1 * (1 / (N : ℝ) ^ 10) := by
        gcongr
        exact (div_le_one₀ (pow_pos hn _)).mpr hpow
      _ = _ := one_mul _
  have hE := gaussian_coefficient_truncation (N + M + 1) hn.le
  exact ((measureReal_mono (μ := gaussianCoefficientMeasure (N + M + 1)) hsub).trans
    (measureReal_union_le A E)).trans (add_le_add hA (by simpa only [Nat.cast_add, Nat.cast_one] using hE))

/-- Restricting one real coefficient sequence gives the canonical difference of polynomial prefixes. -/
theorem gaussianAppendedTailPolynomial_eq_polynomialTail (N M m : ℕ) (hm : m ≤ M) (ε : ℕ → ℝ) :
    gaussianAppendedTailPolynomial N M m (fun k => ε k.val) =
      polynomialTail (fun k => (ε k : ℂ)) (fun _ => 1) N (N + m) := by
  classical
  unfold gaussianAppendedTailPolynomial polynomialTail
  change (∑ k : Fin (N + M + 1),
    (fun j : ℕ => if N < j ∧ j ≤ N + m then monomial j ((ε j : ℂ)) else 0) k.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    if N < j ∧ j ≤ N + m then monomial j ((ε j : ℂ)) else 0) (N + M + 1)]
  simp only [mul_one, C_mul_X_pow_eq_monomial]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega


end Erdos522
