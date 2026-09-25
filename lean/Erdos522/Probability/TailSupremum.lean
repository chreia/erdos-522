/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.RademacherPolynomial
import Erdos522.Probability.ComplexHoeffding
import Erdos522.Analysis.PolynomialGridBounds
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Uniform bounds for appended polynomial tails

Every partial tail in a degree block uses the same vector of coefficient signs.
A union over prefixes and boundary samples, followed by deterministic polynomial
interpolation, controls the entire block on one exceptional event.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

namespace Erdos522
namespace TailSupremum

/-- Coefficients appended after degree `N`, truncated after `m` new coefficients. -/
def appendedTailPolynomial (N M m : ℕ) (ω : LogMoments.SignVector (N + M)) : Polynomial ℂ :=
  ∑ k : Fin (N + M + 1), if N < k.val ∧ k.val ≤ N + m then
    monomial k.val (LogMoments.sign (ω k)) else 0

/-- The coefficient vector of the appended tail evaluated at `z`. -/
def tailCoefficient (N M m : ℕ) (z : ℂ) (k : Fin (N + M + 1)) : ℂ :=
  if N < k.val ∧ k.val ≤ N + m then z ^ k.val else 0

/-- Evaluation is a linear combination of the common block signs. -/
theorem appendedTailPolynomial_eval (N M m : ℕ) (ω : LogMoments.SignVector (N + M)) (z : ℂ) :
    (appendedTailPolynomial N M m ω).eval z =
      LogMoments.complexSignSum (tailCoefficient N M m z) ω := by
  classical
  simp only [appendedTailPolynomial, eval_finsetSum, LogMoments.complexSignSum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : N < k.val ∧ k.val ≤ N + m <;> simp [tailCoefficient, hk]

/-- Restricting a fixed coin sequence gives the canonical difference of polynomial prefixes. -/
theorem appendedTailPolynomial_eq_polynomialTail (N M m : ℕ) (hm : m ≤ M) (ε : ℕ → Bool) :
    appendedTailPolynomial N M m (fun k => ε k.val) =
      polynomialTail (fun k => LogMoments.sign (ε k)) (fun _ => 1) N (N + m) := by
  classical
  unfold appendedTailPolynomial polynomialTail
  change (∑ k : Fin (N + M + 1),
    (fun j : ℕ => if N < j ∧ j ≤ N + m then monomial j (LogMoments.sign (ε j)) else 0) k.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    if N < j ∧ j ≤ N + m then monomial j (LogMoments.sign (ε j)) else 0) (N + M + 1)]
  simp only [mul_one, C_mul_X_pow_eq_monomial]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- There are exactly `M` available coefficients after degree `N`. -/
theorem sum_after_degree_const (N M : ℕ) (C : ℝ) :
    (∑ k : Fin (N + M + 1), if N < k.val then C else 0) = (M : ℝ) * C := by
  classical
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun k : Fin (N + M + 1) => N < k.val) =
      Finset.Ioi (⟨N, by omega⟩ : Fin (N + M + 1)) := by
    ext k
    simp [Fin.lt_def]
  rw [hset]
  simp [Fin.card_Ioi]

/-- The entire block has coefficient energy at most `M B^(2(N+M))` on a disk. -/
theorem tail_coefficient_energy_le (N M m : ℕ) {B : ℝ} (hB : 1 ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ B) :
    ∑ k, ‖tailCoefficient N M m z k‖ ^ 2 ≤ (M : ℝ) * (B ^ (N + M)) ^ 2 := by
  calc
    _ ≤ ∑ k : Fin (N + M + 1), if N < k.val then (B ^ (N + M)) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : N < k.val ∧ k.val ≤ N + m
      · simp only [tailCoefficient, ite_eq_left hk, ite_eq_left hk.1, norm_pow]
        have hp := (pow_le_pow_left₀ (norm_nonneg _) hz k.val).trans
          (pow_le_pow_right₀ hB (Nat.le_of_lt_succ k.isLt))
        exact pow_le_pow_left₀ (by positivity) hp 2
      · simp only [tailCoefficient, ite_eq_right hk, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        split_ifs <;> positivity
    _ = _ := sum_after_degree_const N M _

/-- A deterministic first-derivative bound for every partial tail. -/
theorem tail_derivative_bound (N M m : ℕ) (ω : LogMoments.SignVector (N + M))
    {B : ℝ} (hB : 1 ≤ B) {z : ℂ} (hz : ‖z‖ ≤ B) :
    ‖(appendedTailPolynomial N M m ω).derivative.eval z‖ ≤
      (M : ℝ) * (N + M : ℝ) * B ^ (N + M) := by
  classical
  simp only [appendedTailPolynomial, derivative_sum, eval_finsetSum]
  calc
    _ ≤ ∑ k : Fin (N + M + 1),
      ‖(if N < k.val ∧ k.val ≤ N + m then
        monomial k.val (LogMoments.sign (ω k)) else 0).derivative.eval z‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin (N + M + 1), if N < k.val then
        (N + M : ℝ) * B ^ (N + M) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : N < k.val ∧ k.val ≤ N + m
      · simp only [ite_eq_left hk, ite_eq_left hk.1, derivative_monomial, eval_monomial,
          norm_mul, LogMoments.norm_sign, Complex.norm_natCast, one_mul, norm_pow]
        have hkN : (k.val : ℝ) ≤ N + M := by exact_mod_cast Nat.le_of_lt_succ k.isLt
        have hp := (pow_le_pow_left₀ (norm_nonneg _) hz (k.val - 1)).trans
          (pow_le_pow_right₀ hB (by omega : k.val - 1 ≤ N + M))
        exact mul_le_mul hkN hp (by positivity) (by positivity)
      · simp only [ite_eq_right hk, derivative_zero, eval_zero, norm_zero]
        split_ifs <;> positivity
    _ = _ := by rw [sum_after_degree_const]; ring

/-- All powers up to the block endpoint are controlled by `exp(2K)`. -/
theorem block_radius_pow_le {N M : ℕ} (hN : 0 < N) (hM : M ≤ N)
    {K : ℝ} (hK : 0 ≤ K) :
    (1 + K / N) ^ (N + M) ≤ Real.exp (2 * K) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNM : (N + M : ℝ) ≤ 2 * N := by exact_mod_cast (by omega : N + M ≤ 2 * N)
  have hbase : 1 + K / N ≤ Real.exp (K / N) := by
    simpa only [add_comm] using Real.add_one_le_exp (K / N)
  calc
    _ ≤ Real.exp (K / N) ^ (N + M) := pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((N + M : ℝ) * (K / N)) := by rw [← Real.exp_nat_mul]; push_cast; rfl
    _ ≤ Real.exp (2 * K) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (2 * N) * (K / N) := mul_le_mul_of_nonneg_right hNM (by positivity)
        _ = _ := by field_simp

/-- The common amplitude for every partial tail in a block. -/
def tailAmplitude (N M : ℕ) (K : ℝ) : ℝ :=
  15 * Real.exp (2 * K) * Real.sqrt ((M : ℝ) * Real.log N)

/-- The coefficient energy at the outer radius retains only the block length. -/
theorem annular_tail_energy_le {N M : ℕ} (hN : 0 < N) (hM : M ≤ N)
    (m : ℕ) {K : ℝ} (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ 1 + K / N) :
    ∑ k, ‖tailCoefficient N M m z k‖ ^ 2 ≤ (M : ℝ) * Real.exp (4 * K) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 1 ≤ 1 + K / (N : ℝ) := le_add_of_nonneg_right (by positivity)
  have hp := block_radius_pow_le hN hM hK
  have heq : Real.exp (2 * K) ^ 2 = Real.exp (4 * K) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ (M : ℝ) * ((1 + K / N) ^ (N + M)) ^ 2 := tail_coefficient_energy_le N M m hB hz
    _ ≤ (M : ℝ) * Real.exp (2 * K) ^ 2 := by gcongr
    _ = _ := by rw [heq]

/-- A simultaneous deterministic derivative bound for every partial tail. -/
theorem annular_tail_derivative_bound {N M : ℕ} (hN : 0 < N) (hM : M ≤ N)
    (m : ℕ) (ω : LogMoments.SignVector (N + M)) {K : ℝ} (hK : 0 ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1 + K / N) :
    ‖(appendedTailPolynomial N M m ω).derivative.eval z‖ ≤
      2 * N * M * Real.exp (2 * K) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 1 ≤ 1 + K / (N : ℝ) := le_add_of_nonneg_right (by positivity)
  have hp := block_radius_pow_le hN hM hK
  have hNM : (N + M : ℝ) ≤ 2 * N := by exact_mod_cast (by omega : N + M ≤ 2 * N)
  calc
    _ ≤ (M : ℝ) * (N + M : ℝ) * (1 + K / N) ^ (N + M) := tail_derivative_bound N M m ω hB hz
    _ ≤ (M : ℝ) * (2 * N) * Real.exp (2 * K) := by gcongr
    _ = _ := by ring

/-- At two thirds of the block amplitude, one prefix at one point costs at most `4N⁻²⁵`. -/
theorem appended_tail_point_tail {N M : ℕ} (hN : 2 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    (m : ℕ) {K : ℝ} (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ 1 + K / N) :
    (LogMoments.signMeasure (N + M)).real {ω |
      2 * tailAmplitude N M K / 3 ≤ ‖(appendedTailPolynomial N M m ω).eval z‖} ≤
      4 / (N : ℝ) ^ 25 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hV : 0 < (M : ℝ) * Real.exp (4 * K) := by positivity
  simp_rw [appendedTailPolynomial_eval]
  apply (LogMoments.measure_norm_complexSignSum_ge_le_sharp (tailCoefficient N M m z) hV
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

/-- The deterministic interpolation error is strictly below the remaining third of the amplitude. -/
theorem tail_grid_error_lt {N M : ℕ} (hN : 4 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    {K : ℝ} (_hK : 0 ≤ K) (hKN : K ≤ (N : ℝ)) :
    (2 * N * M * Real.exp (2 * K)) *
        (2 * Real.pi * (1 + K / N) / (N ^ 3 : ℕ)) < tailAmplitude N M K / 3 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast hM
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    apply (Real.le_log_iff_exp_le hN0).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hR : 1 + K / (N : ℝ) ≤ 2 := by
    have := (div_le_one₀ hN0).mpr hKN
    linarith
  have hsqrt : Real.sqrt ((M : ℝ) * Real.log N) ^ 2 = (M : ℝ) * Real.log N :=
    Real.sq_sqrt (by positivity)
  have hp : (64 : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc
      (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ (N : ℝ) ^ 3 := by gcongr
  have hpM : 64 * (M : ℝ) ≤ (N : ℝ) ^ 4 := by
    have := mul_le_mul_of_nonneg_right hp hN0.le
    nlinarith
  have hsqbound : (32 * (M : ℝ)) ^ 2 <
      (5 * Real.sqrt ((M : ℝ) * Real.log N) * (N : ℝ) ^ 2) ^ 2 := by
    have hfirst := mul_le_mul_of_nonneg_left hpM hMpos.le
    have hsecond := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog hMpos.le) (pow_nonneg hN0.le 4)
    rw [mul_one] at hsecond
    simp only [mul_pow, hsqrt]
    norm_num only at *
    nlinarith [sq_pos_of_pos hMpos]
  have hroot : 32 * (M : ℝ) / (N : ℝ) ^ 2 <
      5 * Real.sqrt ((M : ℝ) * Real.log N) := by
    apply (div_lt_iff₀ (pow_pos hN0 _)).mpr
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hsqbound
  have herror : (2 * (N : ℝ) * M * Real.exp (2 * K)) *
      (2 * Real.pi * (1 + K / N) / (N ^ 3 : ℕ)) ≤
      Real.exp (2 * K) * (32 * M / (N : ℝ) ^ 2) := by
    calc
      _ ≤ (2 * (N : ℝ) * M * Real.exp (2 * K)) * (2 * Real.pi * 2 / (N ^ 3 : ℕ)) := by gcongr
      _ = Real.exp (2 * K) * (8 * Real.pi * M / (N : ℝ) ^ 2) := by push_cast; field_simp; ring
      _ ≤ _ := by gcongr; linarith [Real.pi_lt_four]
  apply herror.trans_lt
  calc
    _ < Real.exp (2 * K) * (5 * Real.sqrt ((M : ℝ) * Real.log N)) :=
      mul_lt_mul_of_pos_left hroot (Real.exp_pos _)
    _ = _ := by unfold tailAmplitude; ring

/-- A single exceptional event controls every partial tail and every point of the closed disk. -/
theorem appended_tail_supremum (N M : ℕ) (hN : 4 ≤ N) (hM0 : 1 ≤ M) (hM : M ≤ N)
    {K : ℝ} (hK : 0 ≤ K) (hKN : K ≤ (N : ℝ)) :
    (LogMoments.signMeasure (N + M)).real {ω | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / N ∧ tailAmplitude N M K ≤
        ‖(appendedTailPolynomial N M m ω).eval z‖} ≤ 1 / (N : ℝ) ^ 10 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : 2 ≤ N := by omega
  have hR : 0 < 1 + K / (N : ℝ) := by positivity
  have hJ : 0 < N ^ 3 := pow_pos (by omega) _
  let zgrid := polynomialBoundaryGrid (1 + K / (N : ℝ)) (N ^ 3)
  have hgrid (i : Fin (N ^ 3)) : ‖zgrid i‖ ≤ 1 + K / (N : ℝ) := by
    simp [zgrid, abs_of_pos hR]
  have hsub : {ω : LogMoments.SignVector (N + M) | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ,
      ‖z‖ ≤ 1 + K / N ∧ tailAmplitude N M K ≤
        ‖(appendedTailPolynomial N M m ω).eval z‖} ⊆
      ⋃ p : Fin (M + 1) × Fin (N ^ 3), {ω | 2 * tailAmplitude N M K / 3 ≤
        ‖(appendedTailPolynomial N M p.1.val ω).eval (zgrid p.2)‖} := by
    intro ω hω
    obtain ⟨m, hm, z, hz, hlarge⟩ := hω
    by_contra h
    have hsmall (i : Fin (N ^ 3)) :
        ‖(appendedTailPolynomial N M m ω).eval (zgrid i)‖ ≤ 2 * tailAmplitude N M K / 3 := by
      by_contra! hi
      apply h
      exact Set.mem_iUnion.mpr ⟨(⟨m, by omega⟩, i), hi.le⟩
    have hdisk := polynomial_disk_bound_of_boundary_grid (appendedTailPolynomial N M m ω)
      hR (by positivity : 0 ≤ 2 * N * M * Real.exp (2 * K)) hJ
      (fun w hw => annular_tail_derivative_bound (by omega) hM m ω hK hw) hsmall hz
    have herr := tail_grid_error_lt hN hM0 hM hK hKN
    linarith
  have hprob := (measureReal_mono (μ := LogMoments.signMeasure (N + M)) hsub).trans
    (measureReal_iUnion_fintype_le _)
  have hsum : (∑ p : Fin (M + 1) × Fin (N ^ 3), (LogMoments.signMeasure (N + M)).real
      {ω | 2 * tailAmplitude N M K / 3 ≤
        ‖(appendedTailPolynomial N M p.1.val ω).eval (zgrid p.2)‖}) ≤
      ((M + 1 : ℝ) * (N : ℝ) ^ 3) * (4 / (N : ℝ) ^ 25) := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (M + 1) × Fin (N ^ 3))))
      (fun p _ => appended_tail_point_tail hN2 hM0 hM p.1.val hK (hgrid p.2))
  apply (hprob.trans hsum).trans
  have hMN : (M + 1 : ℝ) ≤ 2 * N := by exact_mod_cast (by omega : M + 1 ≤ 2 * N)
  have hpow : (8 : ℝ) ≤ (N : ℝ) ^ 11 := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
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

end TailSupremum
end Erdos522
