/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.RademacherJets

/-!
# Third moments of annular jet coefficients

The coefficient vectors have size of order `N⁻¹ᐟ²`. Their summed third
moments therefore have size of order `N⁻¹ᐟ²`, uniformly in a fixed annulus.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- The exact squared norm of a value-derivative coefficient on the unit circle. -/
theorem norm_sq_realJetCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (k : Fin (N + 1)) :
    ‖realJetCoefficient N r z k‖ ^ 2 = r ^ (2 * k.val) / N * (1 + ((k.val : ℝ) / N) ^ 2) := by
  have hphase : (z ^ k.val).re ^ 2 + (z ^ k.val).im ^ 2 = 1 := by
    calc
      _ = ‖z ^ k.val‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
      _ = 1 := by simp [norm_pow, hz]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp only [realJetCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hs : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  simp only [mul_pow, div_pow, hs]
  rw [show 2 * k.val = k.val * 2 by omega, pow_mul]
  nlinarith [congrArg (fun t : ℝ => (r ^ k.val) ^ 2 / N * t) hphase,
    congrArg (fun t : ℝ => (r ^ k.val) ^ 2 / N * ((k.val : ℝ) ^ 2 / (N : ℝ) ^ 2) * t) hphase]

/-- A uniform norm bound for a normalized annular coefficient vector. -/
theorem norm_realJetCoefficient_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr : r ≤ 1 + K / N)
    (z : ℂ) (hz : ‖z‖ = 1) (k : Fin (N + 1)) :
    ‖realJetCoefficient N r z k‖ ≤ 2 * Real.exp K / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hk : k.val ≤ N := by omega
  have ht0 : 0 ≤ (k.val : ℝ) / N := by positivity
  have ht1 : (k.val : ℝ) / N ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hk)
  have hrad := radial_power_upper N k.val hN hk K r hK hr0 hr
  have hsquare : ‖realJetCoefficient N r z k‖ ^ 2 ≤ 2 * Real.exp K ^ 2 / N := by
    rw [norm_sq_realJetCoefficient N r z hz k, show 2 * k.val = k.val * 2 by omega, pow_mul]
    have hrad2 : (r ^ k.val) ^ 2 ≤ Real.exp K ^ 2 := by
      nlinarith [pow_nonneg hr0 k.val, Real.exp_pos K]
    calc
      (r ^ k.val) ^ 2 / N * (1 + ((k.val : ℝ) / N) ^ 2) ≤
          Real.exp K ^ 2 / N * 2 := by
        apply mul_le_mul (div_le_div_of_nonneg_right hrad2 hn.le)
          (by nlinarith) (by positivity) (by positivity)
      _ = _ := by ring
  apply (le_div_iff₀ hs).mpr
  have hmul : (‖realJetCoefficient N r z k‖ * Real.sqrt N) ^ 2 ≤ 2 * Real.exp K ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn.le]
    exact (le_div_iff₀ hn).mp hsquare
  nlinarith [norm_nonneg (realJetCoefficient N r z k), Real.exp_pos K]

/-- The summed third moments of the deterministic jet coefficient vectors. -/
theorem sum_third_norm_realJetCoefficient_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr : r ≤ 1 + K / N)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ k, ‖realJetCoefficient N r z k‖ ^ 3) ≤
      16 * Real.exp (3 * K) / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  calc
    _ ≤ ∑ k : Fin (N + 1), (2 * Real.exp K / Real.sqrt N) ^ 3 :=
      Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _)
        (norm_realJetCoefficient_le N hN K r hK hr0 hr z hz k) 3)
    _ = ((N : ℝ) + 1) * (2 * Real.exp K / Real.sqrt N) ^ 3 := by simp
    _ ≤ (2 * N) * (2 * Real.exp K / Real.sqrt N) ^ 3 := by gcongr; linarith
    _ = 16 * Real.exp (3 * K) / Real.sqrt N := by
      rw [show (3 : ℝ) * K = (3 : ℕ) * K by norm_num, Real.exp_nat_mul]
      field_simp
      nlinarith [Real.sq_sqrt hn.le]

/-- The squared norm of a paired coefficient is the sum of the two squared jet norms. -/
theorem norm_sq_realPairedJetCoefficient (N : ℕ) (r s : ℝ) (z w : ℂ)
    (k : Fin (N + 1)) :
    ‖realPairedJetCoefficient N r s z w k‖ ^ 2 =
      ‖realJetCoefficient N r z k‖ ^ 2 + ‖realJetCoefficient N s w k‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.sum_univ_zero,
    realPairedJetCoefficient, realJetCoefficient]
  norm_num
  ring

/-- A uniform norm bound for a paired normalized coefficient vector. -/
theorem norm_realPairedJetCoefficient_le (N : ℕ) (hN : 0 < N) (K r s : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (k : Fin (N + 1)) :
    ‖realPairedJetCoefficient N r s z w k‖ ≤ 4 * Real.exp K / Real.sqrt N := by
  have he := norm_sq_realPairedJetCoefficient N r s z w k
  have hr' := norm_realJetCoefficient_le N hN K r hK hr0 hr z hz k
  have hs' := norm_realJetCoefficient_le N hN K s hK hs0 hs w hw k
  have htriangle : ‖realPairedJetCoefficient N r s z w k‖ ≤
      ‖realJetCoefficient N r z k‖ + ‖realJetCoefficient N s w k‖ := by
    nlinarith [norm_nonneg (realPairedJetCoefficient N r s z w k),
      norm_nonneg (realJetCoefficient N r z k), norm_nonneg (realJetCoefficient N s w k),
      mul_nonneg (norm_nonneg (realJetCoefficient N r z k))
        (norm_nonneg (realJetCoefficient N s w k))]
  calc
    _ ≤ ‖realJetCoefficient N r z k‖ + ‖realJetCoefficient N s w k‖ := htriangle
    _ ≤ (2 * Real.exp K / Real.sqrt N) + (2 * Real.exp K / Real.sqrt N) := add_le_add hr' hs'
    _ = _ := by ring

/-- The summed third moments of paired annular jet coefficients. -/
theorem sum_third_norm_realPairedJetCoefficient_le (N : ℕ) (hN : 0 < N) (K r s : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    (∑ k, ‖realPairedJetCoefficient N r s z w k‖ ^ 3) ≤
      128 * Real.exp (3 * K) / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ ∑ k : Fin (N + 1), (4 * Real.exp K / Real.sqrt N) ^ 3 :=
      Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _)
        (norm_realPairedJetCoefficient_le N hN K r s hK hr0 hs0 hr hs z w hz hw k) 3)
    _ = ((N : ℝ) + 1) * (4 * Real.exp K / Real.sqrt N) ^ 3 := by simp
    _ ≤ (2 * N) * (4 * Real.exp K / Real.sqrt N) ^ 3 := by gcongr; linarith
    _ = 128 * Real.exp (3 * K) / Real.sqrt N := by
      rw [show (3 : ℝ) * K = (3 : ℕ) * K by norm_num, Real.exp_nat_mul]
      field_simp
      nlinarith [Real.sq_sqrt hn.le]

end Erdos522
