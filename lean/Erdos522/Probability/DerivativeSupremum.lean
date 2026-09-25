/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.RademacherPolynomial
import Erdos522.Probability.ComplexHoeffding
import Erdos522.Analysis.PolynomialGridBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Derivative suprema of Rademacher polynomials

A finite boundary grid converts complex Hoeffding bounds into a supremum estimate.
The deterministic derivative bound controls interpolation between consecutive
samples; the maximum modulus principle extends the boundary estimate to the disk.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace Erdos522
namespace DerivativeSupremum

/-- The deterministic coefficient at a point in an iterated derivative. -/
def derivativeCoefficient (N m : ℕ) (z : ℂ) (k : Fin (N + 1)) : ℂ :=
  (k.val.descFactorial m : ℂ) * z ^ (k.val - m)

/-- Iterated derivatives are complex linear combinations of the original signs. -/
theorem eval_iterate_derivative (N m : ℕ) (ω : LogMoments.SignVector N) (z : ℂ) :
    (Polynomial.derivative^[m] (rademacherPolynomial N ω)).eval z =
      LogMoments.complexSignSum (derivativeCoefficient N m z) ω := by
  classical
  unfold rademacherPolynomial LogMoments.signedPolynomial
  simp only [mul_one, ← C_mul_X_pow_eq_monomial, iterate_derivative_sum,
    iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    LogMoments.complexSignSum, derivativeCoefficient]

/-- Each differentiated coefficient has a degree-uniform disk bound. -/
theorem norm_derivativeCoefficient_le (N m : ℕ) {B : ℝ} (hB : 1 ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ B) (k : Fin (N + 1)) :
    ‖derivativeCoefficient N m z k‖ ≤ (N : ℝ) ^ m * B ^ N := by
  rw [derivativeCoefficient, norm_mul, Complex.norm_natCast, norm_pow]
  have hc : (k.val.descFactorial m : ℝ) ≤ (N : ℝ) ^ m := by
    exact_mod_cast (k.val.descFactorial_le_pow m).trans
      (Nat.pow_le_pow_left (Nat.le_of_lt_succ k.isLt) m)
  have hp := (pow_le_pow_left₀ (norm_nonneg _) hz (k.val - m)).trans
    (pow_le_pow_right₀ hB (by omega : k.val - m ≤ N))
  exact mul_le_mul hc hp (by positivity) (by positivity)

/-- The squared coefficient energy of an iterated derivative on a disk. -/
theorem derivative_coefficient_energy_le (N m : ℕ) {B : ℝ} (hB : 1 ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ B) :
    ∑ k, ‖derivativeCoefficient N m z k‖ ^ 2 ≤
      (N + 1 : ℝ) * ((N : ℝ) ^ m * B ^ N) ^ 2 := by
  calc
    _ ≤ ∑ _k : Fin (N + 1), ((N : ℝ) ^ m * B ^ N) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_derivativeCoefficient_le N m hB hz k) 2
    _ = _ := by simp

/-- A deterministic supremum bound for any iterated derivative. -/
theorem norm_iterate_derivative_le (N m : ℕ) (ω : LogMoments.SignVector N)
    {B : ℝ} (hB : 1 ≤ B) {z : ℂ} (hz : ‖z‖ ≤ B) :
    ‖(Polynomial.derivative^[m] (rademacherPolynomial N ω)).eval z‖ ≤
      (N + 1 : ℝ) * ((N : ℝ) ^ m * B ^ N) := by
  rw [eval_iterate_derivative, LogMoments.complexSignSum]
  calc
    _ ≤ ∑ k, ‖LogMoments.sign (ω k) * derivativeCoefficient N m z k‖ := norm_sum_le _ _
    _ = ∑ k, ‖derivativeCoefficient N m z k‖ := by simp only [norm_mul, LogMoments.norm_sign, one_mul]
    _ ≤ ∑ _k : Fin (N + 1), (N : ℝ) ^ m * B ^ N := by
      exact Finset.sum_le_sum (fun k _ => norm_derivativeCoefficient_le N m hB hz k)
    _ = _ := by simp

/-- Exponential control of the enlarged radial power. -/
theorem annular_radius_pow_le {N : ℕ} (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K) :
    (1 + (K + 1) / N) ^ N ≤ Real.exp (K + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase : 1 + (K + 1) / N ≤ Real.exp ((K + 1) / N) := by
    simpa only [add_comm] using Real.add_one_le_exp ((K + 1) / N)
  calc
    _ ≤ Real.exp ((K + 1) / N) ^ N := pow_le_pow_left₀ (by positivity) hbase N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; field_simp

/-- The second derivative has coefficient energy at most `2 exp(2K+2) N^5`. -/
theorem second_derivative_energy_le {N : ℕ} (hN : 1 ≤ N) {K : ℝ} (hK : 0 ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
    ∑ k, ‖derivativeCoefficient N 2 z k‖ ^ 2 ≤
      2 * Real.exp (2 * K + 2) * (N : ℝ) ^ 5 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase := derivative_coefficient_energy_le N 2 (by linarith [div_nonneg (by linarith : 0 ≤ K + 1) hN0.le] : 1 ≤ 1 + (K + 1) / N) hz
  have hpow := annular_radius_pow_le (by omega : 0 < N) hK
  have heq : Real.exp (K + 1) ^ 2 = Real.exp (2 * K + 2) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ (N + 1 : ℝ) * ((N : ℝ) ^ 2 * (1 + (K + 1) / N) ^ N) ^ 2 := hbase
    _ ≤ (2 * N) * ((N : ℝ) ^ 2 * Real.exp (K + 1)) ^ 2 := by gcongr; linarith
    _ = _ := by rw [mul_pow, heq]; ring

/-- A deterministic third derivative bound on the enlarged disk. -/
theorem third_derivative_bound {N : ℕ} (hN : 1 ≤ N) (ω : LogMoments.SignVector N)
    {K : ℝ} (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
    ‖(rademacherPolynomial N ω).derivative.derivative.derivative.eval z‖ ≤
      2 * Real.exp (K + 1) * (N : ℝ) ^ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase := norm_iterate_derivative_le N 3 ω
    (by linarith [div_nonneg (by linarith : 0 ≤ K + 1) hN0.le] : 1 ≤ 1 + (K + 1) / N) hz
  change ‖(rademacherPolynomial N ω).derivative.derivative.derivative.eval z‖ ≤ _ at hbase
  have hpow := annular_radius_pow_le (by omega : 0 < N) hK
  calc
    _ ≤ (N + 1 : ℝ) * ((N : ℝ) ^ 3 * (1 + (K + 1) / N) ^ N) := hbase
    _ ≤ (2 * N) * ((N : ℝ) ^ 3 * Real.exp (K + 1)) := by gcongr; linarith
    _ = _ := by ring

/-- The second-derivative envelope, with the square-root scaling kept explicit. -/
def secondDerivativeEnvelope (N : ℕ) (K : ℝ) : ℝ :=
  100 * Real.exp (K + 4) * Real.sqrt ((N : ℝ) ^ 5 * Real.log N)

/-- The second derivative at any point in the enlarged disk has failure at most `4N⁻¹⁰⁰`
at half of the uniform envelope. -/
theorem second_derivative_point_tail {N : ℕ} (hN : 2 ≤ N) {K : ℝ} (hK : 0 ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
    (LogMoments.signMeasure N).real {ω |
      secondDerivativeEnvelope N K / 2 ≤
        ‖(rademacherPolynomial N ω).derivative.derivative.eval z‖} ≤
      4 / (N : ℝ) ^ 100 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hV : 0 < 2 * Real.exp (2 * K + 2) * (N : ℝ) ^ 5 := by positivity
  have htail := LogMoments.measure_norm_complexSignSum_ge_le
    (derivativeCoefficient N 2 z) hV (second_derivative_energy_le (by omega) hK hz)
    (by unfold secondDerivativeEnvelope; positivity : 0 ≤ secondDerivativeEnvelope N K / 2)
  change (LogMoments.signMeasure N).real {ω |
      secondDerivativeEnvelope N K / 2 ≤
        ‖(Polynomial.derivative^[2] (rademacherPolynomial N ω)).eval z‖} ≤ _
  simp_rw [eval_iterate_derivative]
  apply htail.trans
  have hexp : Real.exp (2 * K + 2) ≤ Real.exp (K + 4) ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hproduct := mul_le_mul_of_nonneg_right hexp
    (mul_nonneg (pow_nonneg hN0.le 5) hlog)
  have hsquare : (secondDerivativeEnvelope N K / 2) ^ 2 =
      2500 * Real.exp (K + 4) ^ 2 * (N : ℝ) ^ 5 * Real.log N := by
    unfold secondDerivativeEnvelope
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hquot : 100 * Real.log N ≤ (secondDerivativeEnvelope N K / 2) ^ 2 /
      (8 * (2 * Real.exp (2 * K + 2) * (N : ℝ) ^ 5)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [hsquare]
    nlinarith [mul_nonneg (Real.exp_nonneg (2 * K + 2))
      (mul_nonneg (pow_nonneg hN0.le 5) hlog)]
  calc
    _ ≤ 4 * Real.exp (-(100 * Real.log N)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      exact neg_le_neg hquot
    _ = _ := by
      rw [Real.exp_neg, show (100 : ℝ) = (100 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hN0, div_eq_mul_inv]

/-- The interpolation error from `N³` boundary samples fits in half of the envelope. -/
theorem second_derivative_grid_error_le {N : ℕ} (hN : 2 ≤ N) {K : ℝ} (_hK : 0 ≤ K)
    (hKN : K + 1 ≤ (N : ℝ)) :
    (2 * Real.exp (K + 1) * (N : ℝ) ^ 4) *
        (2 * Real.pi * (1 + (K + 1) / N) / (N ^ 3 : ℕ)) ≤
      secondDerivativeEnvelope N K / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : (1 / 2 : ℝ) ≤ Real.log (N : ℝ) :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hN2)
  have hR : 1 + (K + 1) / (N : ℝ) ≤ 2 := by
    have := (div_le_one₀ hN0).mpr hKN
    linarith
  have hsqrt : (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 5 * Real.log N) := by
    apply Real.le_sqrt_of_sq_le
    have hp : 1 ≤ (N : ℝ) ^ 3 * Real.log N := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN2 3]
    nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.mpr hp)]
  have hexp : Real.exp (K + 1) ≤ Real.exp (K + 4) := Real.exp_le_exp.mpr (by linarith)
  have herror : (2 * Real.exp (K + 1) * (N : ℝ) ^ 4) *
      (2 * Real.pi * (1 + (K + 1) / N) / (N ^ 3 : ℕ)) ≤
      8 * Real.pi * Real.exp (K + 1) * N := by
    calc
      _ ≤ (2 * Real.exp (K + 1) * (N : ℝ) ^ 4) * (2 * Real.pi * 2 / (N ^ 3 : ℕ)) := by
        gcongr
      _ = _ := by push_cast; field_simp; ring
  apply herror.trans
  unfold secondDerivativeEnvelope
  have hpi : 8 * Real.pi ≤ (50 : ℝ) := by linarith [Real.pi_lt_four]
  calc
    8 * Real.pi * Real.exp (K + 1) * N ≤ 50 * Real.exp (K + 4) *
      Real.sqrt ((N : ℝ) ^ 5 * Real.log N) := by gcongr
    _ = _ := by ring

/-- The actual second-derivative supremum bound on the full closed disk. -/
theorem second_derivative_supremum (N : ℕ) (hN : 2 ≤ N) {K : ℝ} (hK : 0 ≤ K)
    (hKN : K + 1 ≤ (N : ℝ)) :
    (LogMoments.signMeasure N).real {ω | ∃ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N ∧ secondDerivativeEnvelope N K <
        ‖(rademacherPolynomial N ω).derivative.derivative.eval z‖} ≤
      1 / (N : ℝ) ^ 10 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR : 0 < 1 + (K + 1) / (N : ℝ) := by positivity
  have hJ : 0 < N ^ 3 := pow_pos (by omega) _
  let zgrid := polynomialBoundaryGrid (1 + (K + 1) / (N : ℝ)) (N ^ 3)
  have hgrid (i : Fin (N ^ 3)) : ‖zgrid i‖ ≤ 1 + (K + 1) / (N : ℝ) := by
    simp [zgrid, abs_of_pos hR]
  have hsub : {ω : LogMoments.SignVector N | ∃ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N ∧ secondDerivativeEnvelope N K <
        ‖(rademacherPolynomial N ω).derivative.derivative.eval z‖} ⊆
      ⋃ i : Fin (N ^ 3), {ω | secondDerivativeEnvelope N K / 2 ≤
        ‖(rademacherPolynomial N ω).derivative.derivative.eval (zgrid i)‖} := by
    intro ω hω
    obtain ⟨z, hz, hlarge⟩ := hω
    by_contra h
    have hsmall : ∀ i, ‖(rademacherPolynomial N ω).derivative.derivative.eval (zgrid i)‖ ≤
        secondDerivativeEnvelope N K / 2 := by
      have hh : ∀ i, ‖(rademacherPolynomial N ω).derivative.derivative.eval (zgrid i)‖ <
          secondDerivativeEnvelope N K / 2 := by
        simpa only [Set.mem_iUnion, Set.mem_ofPred, not_exists, not_le] using h
      exact fun i => (hh i).le
    have hdisk := polynomial_disk_bound_of_boundary_grid
      (rademacherPolynomial N ω).derivative.derivative hR
      (by positivity : 0 ≤ 2 * Real.exp (K + 1) * (N : ℝ) ^ 4) hJ
      (fun w hw => third_derivative_bound (by omega) ω hK hw) hsmall hz
    have herr := second_derivative_grid_error_le hN hK hKN
    linarith
  have hprob := (measureReal_mono (μ := LogMoments.signMeasure N) hsub).trans
    (measureReal_iUnion_fintype_le _)
  have hsum : (∑ i : Fin (N ^ 3), (LogMoments.signMeasure N).real
      {ω | secondDerivativeEnvelope N K / 2 ≤
        ‖(rademacherPolynomial N ω).derivative.derivative.eval (zgrid i)‖}) ≤
      (N : ℝ) ^ 3 * (4 / (N : ℝ) ^ 100) := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (N ^ 3))))
      (fun i _ => second_derivative_point_tail hN hK (hgrid i))
  apply (hprob.trans hsum).trans
  have hpow : (4 : ℝ) ≤ (N : ℝ) ^ 87 := by
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    calc
      (4 : ℝ) ≤ 2 ^ 87 := by norm_num
      _ ≤ (N : ℝ) ^ 87 := by gcongr
  calc
    _ = (4 / (N : ℝ) ^ 87) * (1 / (N : ℝ) ^ 10) := by field_simp
    _ ≤ 1 * (1 / (N : ℝ) ^ 10) := by
      gcongr
      exact (div_le_one₀ (pow_pos hN0 _)).mpr hpow
    _ = _ := one_mul _

/-- The envelope agrees exactly with the `N^(5/2) sqrt(log N)` normalization. -/
theorem secondDerivativeEnvelope_eq (N : ℕ) (K : ℝ) :
    secondDerivativeEnvelope N K =
      (100 * Real.exp (K + 4)) * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) := by
  have hpow : Real.sqrt ((N : ℝ) ^ 5) = (N : ℝ) ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
    congr 1
    norm_num
  rw [secondDerivativeEnvelope, Real.sqrt_mul (by positivity), hpow]
  ring

/-- The simultaneous second-derivative envelope with its power normalization displayed. -/
theorem annular_derivative_supremum (N : ℕ) (hN : 2 ≤ N) {K : ℝ} (hK : 0 ≤ K)
    (hKN : K + 1 ≤ (N : ℝ)) :
    (LogMoments.signMeasure N).real {ω | ∃ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N ∧
      (100 * Real.exp (K + 4)) * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) <
        ‖(rademacherPolynomial N ω).derivative.derivative.eval z‖} ≤
      1 / (N : ℝ) ^ 10 := by
  simpa only [secondDerivativeEnvelope_eq] using second_derivative_supremum N hN hK hKN

end DerivativeSupremum
end Erdos522
