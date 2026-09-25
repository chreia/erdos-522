/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BoundedPolynomialSuprema

/-!
# Maximal appended tails for bounded complex coefficients

A single coefficient vector supplies every tail in a degree block. A finite
union over truncation lengths and boundary samples controls all of them on
the same exceptional event, with the coefficient bound appearing only in the
amplitude.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522
namespace BoundedTailSupremum

/-- The partial tail extracted from a common block coefficient vector. -/
def appendedTailPolynomial (N M m : ℕ) (a : Fin (N + M + 1) → ℂ) : Polynomial ℂ :=
  ∑ k : Fin (N + M + 1), if N < k.val ∧ k.val ≤ N + m then monomial k.val (a k) else 0

theorem appendedTailPolynomial_eval (N M m : ℕ) (a : Fin (N + M + 1) → ℂ) (z : ℂ) :
    (appendedTailPolynomial N M m a).eval z =
      ∑ k, TailSupremum.tailCoefficient N M m z k * a k := by
  classical
  simp only [appendedTailPolynomial, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : N < k.val ∧ k.val ≤ N + m <;>
    simp [TailSupremum.tailCoefficient, hk, mul_comm]

/-- The tail vector is the difference of prefixes of the same infinite
coefficient sequence. -/
theorem appendedTailPolynomial_eq_polynomialTail (N M m : ℕ) (hm : m ≤ M) (a : ℕ → ℂ) :
    appendedTailPolynomial N M m (fun k => a k.val) =
      polynomialTail a (fun _ => 1) N (N + m) := by
  classical
  unfold appendedTailPolynomial polynomialTail
  change (∑ k : Fin (N + M + 1),
    (fun j : ℕ => if N < j ∧ j ≤ N + m then monomial j (a j) else 0) k.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    if N < j ∧ j ≤ N + m then monomial j (a j) else 0) (N + M + 1)]
  simp only [mul_one, C_mul_X_pow_eq_monomial]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- A deterministic derivative bound for every bounded-coefficient partial tail. -/
theorem tail_derivative_bound (N M m : ℕ) (a : Fin (N + M + 1) → ℂ)
    {B R : ℝ} (hB : 0 ≤ B) (ha : ∀ k, ‖a k‖ ≤ B) (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(appendedTailPolynomial N M m a).derivative.eval z‖ ≤
      B * ((M : ℝ) * (N + M : ℝ) * R ^ (N + M)) := by
  classical
  simp only [appendedTailPolynomial, derivative_sum, eval_finsetSum]
  calc
    _ ≤ ∑ k : Fin (N + M + 1),
      ‖(if N < k.val ∧ k.val ≤ N + m then monomial k.val (a k) else 0).derivative.eval z‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k : Fin (N + M + 1), if N < k.val then
        B * ((N + M : ℝ) * R ^ (N + M)) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : N < k.val ∧ k.val ≤ N + m
      · simp only [ite_eq_left hk, ite_eq_left hk.1, derivative_monomial, eval_monomial,
          norm_mul, Complex.norm_natCast, norm_pow]
        have hkN : (k.val : ℝ) ≤ N + M := by exact_mod_cast Nat.le_of_lt_succ k.isLt
        have hp := (pow_le_pow_left₀ (norm_nonneg _) hz (k.val - 1)).trans
          (pow_le_pow_right₀ hR (by omega : k.val - 1 ≤ N + M))
        calc
          _ ≤ B * (N + M : ℝ) * R ^ (N + M) := by gcongr; exact ha k
          _ = _ := by ring
      · simp only [ite_eq_right hk, derivative_zero, eval_zero, norm_zero]
        split_ifs <;> positivity
    _ = _ := by rw [TailSupremum.sum_after_degree_const]; ring

/-- The annular derivative envelope is uniform in the partial-tail length. -/
theorem annular_tail_derivative_bound {N M : ℕ} (hN : 0 < N) (hM : M ≤ N)
    (m : ℕ) (a : Fin (N + M + 1) → ℂ) {B K : ℝ} (hB : 0 ≤ B)
    (ha : ∀ k, ‖a k‖ ≤ B) (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ 1 + K / N) :
    ‖(appendedTailPolynomial N M m a).derivative.eval z‖ ≤
      B * (2 * N * M * Real.exp (2 * K)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 1 ≤ 1 + K / (N : ℝ) := le_add_of_nonneg_right (by positivity)
  have hp := TailSupremum.block_radius_pow_le hN hM hK
  have hNM : (N + M : ℝ) ≤ 2 * N := by exact_mod_cast (by omega : N + M ≤ 2 * N)
  apply (tail_derivative_bound N M m a hB ha hR hz).trans
  apply mul_le_mul_of_nonneg_left _ hB
  calc
    _ ≤ (M : ℝ) * (2 * N) * Real.exp (2 * K) := by gcongr
    _ = _ := by ring

/-- At two thirds of the scaled amplitude, one partial tail at one point
has failure probability at most `4N⁻²⁵`. -/
theorem appended_tail_point_tail {N M : ℕ} (hN : 2 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    (μ : Fin (N + M + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (m : ℕ) {B K : ℝ} (hB : 0 < B) (hK : 0 ≤ K)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0)
    {z : ℂ} (hz : ‖z‖ ≤ 1 + K / N) :
    (Measure.pi μ).real {a | B * (2 * TailSupremum.tailAmplitude N M K / 3) ≤
      ‖(appendedTailPolynomial N M m a).eval z‖} ≤ 4 / (N : ℝ) ^ 25 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hV : 0 < (M : ℝ) * Real.exp (4 * K) := by positivity
  simp_rw [appendedTailPolynomial_eval]
  apply (BoundedPolynomialSuprema.measure_scaled_complex_sum_ge_le μ
    (TailSupremum.tailCoefficient N M m z) hB hV
    (TailSupremum.annular_tail_energy_le (by omega) hM m hK hz) hbound hmean
    (by unfold TailSupremum.tailAmplitude; positivity)).trans
  have heq : (2 * TailSupremum.tailAmplitude N M K / 3) ^ 2 /
      (4 * ((M : ℝ) * Real.exp (4 * K))) = 25 * Real.log N := by
    unfold TailSupremum.tailAmplitude
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hexp : Real.exp (2 * K) ^ 2 = Real.exp (4 * K) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    field_simp
    ring
  rw [neg_div, heq, Real.exp_neg, show (25 : ℝ) = (25 : ℕ) by norm_num,
    Real.exp_nat_mul, Real.exp_log hN0, div_eq_mul_inv]

/-- Every appended tail in the whole block is controlled on the same
exceptional event, under the actual independent coefficient law. -/
theorem appended_tail_supremum (N M : ℕ) (hN : 4 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    (μ : Fin (N + M + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    {B K : ℝ} (hB : 0 < B) (hK : 0 ≤ K) (hKN : K ≤ (N : ℝ))
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0) :
    (Measure.pi μ).real {a | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / N ∧ B * TailSupremum.tailAmplitude N M K ≤
        ‖(appendedTailPolynomial N M m a).eval z‖} ≤ 1 / (N : ℝ) ^ 10 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR : 0 < 1 + K / (N : ℝ) := by positivity
  have hd : ∀ᵐ a ∂Measure.pi μ, ∀ (i : Fin (M + 1)) z, ‖z‖ ≤ 1 + K / N →
      ‖(appendedTailPolynomial N M i.val a).derivative.eval z‖ ≤
        B * (2 * N * M * Real.exp (2 * K)) := by
    filter_upwards [BoundedPolynomialSuprema.ae_coordinate_norm_le μ hbound] with a ha
    exact fun _ _ hz => annular_tail_derivative_bound (by omega) hM _ a hB.le ha hK hz
  have hp := BoundedPolynomialSuprema.measure_polynomial_disk_supremum_ge_le (Measure.pi μ)
    (fun (i : Fin (M + 1)) a => appendedTailPolynomial N M i.val a)
    hR (by positivity) (pow_pos (by omega : 0 < N) 3) hd
    (fun i j => appended_tail_point_tail (by omega) hM0 hM μ i.val hB hK hbound hmean
      (by simp [abs_of_pos hR] : ‖polynomialBoundaryGrid (1 + K / N) (N ^ 3) j‖ ≤ _))
    (show B * (2 * TailSupremum.tailAmplitude N M K / 3) +
      (B * (2 * N * M * Real.exp (2 * K))) *
        (2 * Real.pi * (1 + K / N) / (N ^ 3 : ℕ)) < B * TailSupremum.tailAmplitude N M K from by
      have he := mul_lt_mul_of_pos_left (TailSupremum.tail_grid_error_lt hN hM0 hM hK hKN) hB
      nlinarith)
  have hevent : {a : Fin (N + M + 1) → ℂ | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / N ∧ B * TailSupremum.tailAmplitude N M K ≤
        ‖(appendedTailPolynomial N M m a).eval z‖} =
      {a | ∃ i : Fin (M + 1), ∃ z : ℂ, ‖z‖ ≤ 1 + K / N ∧
        B * TailSupremum.tailAmplitude N M K ≤ ‖(appendedTailPolynomial N M i.val a).eval z‖} := by
    ext a
    constructor
    · rintro ⟨m, hm, hz⟩
      exact ⟨⟨m, by omega⟩, hz⟩
    · rintro ⟨i, hz⟩
      exact ⟨i.val, by omega, hz⟩
  rw [hevent]
  apply hp.trans
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hMN : (M + 1 : ℝ) ≤ 2 * N := by exact_mod_cast (by omega : M + 1 ≤ 2 * N)
  have hpow : (8 : ℝ) ≤ (N : ℝ) ^ 11 := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    calc
      (8 : ℝ) ≤ 2 ^ 11 := by norm_num
      _ ≤ (N : ℝ) ^ 11 := by gcongr
  calc
    _ ≤ ((2 * N) * (N : ℝ) ^ 3) * (4 / (N : ℝ) ^ 25) := by gcongr
    _ = (8 / (N : ℝ) ^ 11) * (1 / (N : ℝ) ^ 10) := by field_simp; ring
    _ ≤ 1 * (1 / (N : ℝ) ^ 10) := by
      gcongr
      exact (div_le_one₀ (pow_pos hN0 _)).mpr hpow
    _ = _ := one_mul _

end BoundedTailSupremum
end Erdos522
