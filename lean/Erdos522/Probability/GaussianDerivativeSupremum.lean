/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianTails
import Erdos522.Probability.GaussianFourierLogarithmicMoments
import Erdos522.Probability.DerivativeSupremum

/-!
# Derivative suprema of Gaussian polynomials

Scalar Gaussian tails control a boundary grid. On the coefficient truncation
`max |gₖ| ≤ N`, the enlarged grid of `N⁴` points has the same interpolation
error as the bounded-coefficient argument.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522
open DerivativeSupremum

/-- Iterated derivatives retain their deterministic coefficient vectors. -/
theorem gaussian_eval_iterate_derivative (N m : ℕ) (g : Fin (N + 1) → ℝ) (z : ℂ) :
    (Polynomial.derivative^[m] (gaussianPolynomial N g)).eval z =
      complexGaussianSum (derivativeCoefficient N m z) g := by
  classical
  unfold gaussianPolynomial
  simp only [← C_mul_X_pow_eq_monomial, iterate_derivative_sum,
    iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    complexGaussianSum, derivativeCoefficient]

/-- A coefficient truncation gives a deterministic derivative envelope. -/
theorem gaussian_norm_iterate_derivative_le (N m : ℕ) (g : Fin (N + 1) → ℝ)
    {C B : ℝ} (hC : 0 ≤ C) (hg : ∀ k, |g k| ≤ C)
    (hB : 1 ≤ B) {z : ℂ} (hz : ‖z‖ ≤ B) :
    ‖(Polynomial.derivative^[m] (gaussianPolynomial N g)).eval z‖ ≤
      C * ((N + 1 : ℝ) * ((N : ℝ) ^ m * B ^ N)) := by
  rw [gaussian_eval_iterate_derivative, complexGaussianSum]
  calc
    _ ≤ ∑ k, ‖(g k : ℂ) * derivativeCoefficient N m z k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin (N + 1), C * ((N : ℝ) ^ m * B ^ N) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hg k) (norm_derivativeCoefficient_le N m hB hz k) (norm_nonneg _) hC
    _ = _ := by simp; ring

/-- The third derivative gains exactly the coefficient truncation factor. -/
theorem gaussian_third_derivative_bound {N : ℕ} (hN : 1 ≤ N)
    (g : Fin (N + 1) → ℝ) (hg : ∀ k, |g k| ≤ (N : ℝ))
    {K : ℝ} (hK : 0 ≤ K) {z : ℂ} (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
    ‖(gaussianPolynomial N g).derivative.derivative.derivative.eval z‖ ≤
      2 * Real.exp (K + 1) * (N : ℝ) ^ 5 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase := gaussian_norm_iterate_derivative_le N 3 g hN0.le hg
    (by linarith [div_nonneg (by linarith : 0 ≤ K + 1) hN0.le] : 1 ≤ 1 + (K + 1) / N) hz
  change ‖(gaussianPolynomial N g).derivative.derivative.derivative.eval z‖ ≤ _ at hbase
  have hpow := annular_radius_pow_le (by omega : 0 < N) hK
  calc
    _ ≤ (N : ℝ) * ((N + 1 : ℝ) * ((N : ℝ) ^ 3 * (1 + (K + 1) / N) ^ N)) := hbase
    _ ≤ (N : ℝ) * ((2 * N) * ((N : ℝ) ^ 3 * Real.exp (K + 1))) := by gcongr; linarith
    _ = _ := by ring

/-- The second derivative at any point in the enlarged disk has failure at most `4N⁻¹⁰⁰`
at half of the uniform envelope. -/
theorem gaussian_second_derivative_point_tail {N : ℕ} (hN : 2 ≤ N) {K : ℝ} (hK : 0 ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
    (gaussianCoefficientMeasure (N + 1)).real {ω |
      secondDerivativeEnvelope N K / 2 ≤
        ‖(gaussianPolynomial N ω).derivative.derivative.eval z‖} ≤
      4 / (N : ℝ) ^ 100 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hV : 0 < 2 * Real.exp (2 * K + 2) * (N : ℝ) ^ 5 := by positivity
  have htail := measure_norm_complexGaussianSum_ge_le
    (derivativeCoefficient N 2 z) hV (second_derivative_energy_le (by omega) hK hz)
    (by unfold secondDerivativeEnvelope; positivity : 0 ≤ secondDerivativeEnvelope N K / 2)
  change (gaussianCoefficientMeasure (N + 1)).real {ω |
      secondDerivativeEnvelope N K / 2 ≤
        ‖(Polynomial.derivative^[2] (gaussianPolynomial N ω)).eval z‖} ≤ _
  simp_rw [gaussian_eval_iterate_derivative]
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


/-- Increasing the boundary grid to `N⁴` absorbs the coefficient truncation factor `N`. -/
theorem gaussian_second_derivative_grid_error_le {N : ℕ} (hN : 2 ≤ N) {K : ℝ}
    (hK : 0 ≤ K) (hKN : K + 1 ≤ (N : ℝ)) :
    (2 * Real.exp (K + 1) * (N : ℝ) ^ 5) *
      (2 * Real.pi * (1 + (K + 1) / N) / (N ^ 4 : ℕ)) ≤ secondDerivativeEnvelope N K / 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (2 * Real.exp (K + 1) * (N : ℝ) ^ 5) *
      (2 * Real.pi * (1 + (K + 1) / N) / (N ^ 4 : ℕ)) =
      (2 * Real.exp (K + 1) * (N : ℝ) ^ 4) *
        (2 * Real.pi * (1 + (K + 1) / N) / (N ^ 3 : ℕ)) := by
    push_cast
    field_simp
  rw [he]
  exact second_derivative_grid_error_le hN hK hKN

/-- The Gaussian second-derivative supremum has a polynomial failure budget
plus the explicitly retained coefficient-truncation probability. -/
theorem gaussian_second_derivative_supremum (N : ℕ) (hN : 2 ≤ N) {K : ℝ}
    (hK : 0 ≤ K) (hKN : K + 1 ≤ (N : ℝ)) :
    (gaussianCoefficientMeasure (N + 1)).real {g | ∃ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N ∧ secondDerivativeEnvelope N K <
        ‖(gaussianPolynomial N g).derivative.derivative.eval z‖} ≤
      1 / (N : ℝ) ^ 10 + 2 * (N + 1) * Real.exp (-(N : ℝ) ^ 2 / 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : 0 < 1 + (K + 1) / (N : ℝ) := by positivity
  have hJ : 0 < N ^ 4 := pow_pos (by omega) _
  let zgrid := polynomialBoundaryGrid (1 + (K + 1) / (N : ℝ)) (N ^ 4)
  have hgrid (i : Fin (N ^ 4)) : ‖zgrid i‖ ≤ 1 + (K + 1) / (N : ℝ) := by
    simp [zgrid, abs_of_pos hR]
  let E : Set (Fin (N + 1) → ℝ) := {g | ∃ k, (N : ℝ) < |g k|}
  let A : Set (Fin (N + 1) → ℝ) := ⋃ i : Fin (N ^ 4), {g |
    secondDerivativeEnvelope N K / 2 ≤ ‖(gaussianPolynomial N g).derivative.derivative.eval (zgrid i)‖}
  have hsub : {g : Fin (N + 1) → ℝ | ∃ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N ∧ secondDerivativeEnvelope N K <
        ‖(gaussianPolynomial N g).derivative.derivative.eval z‖} ⊆ A ∪ E := by
    intro g hg
    by_cases hgE : g ∈ E
    · exact Or.inr hgE
    left
    have hcoeff : ∀ k, |g k| ≤ (N : ℝ) := by
      intro k
      exact le_of_not_gt (fun hk => hgE ⟨k, hk⟩)
    obtain ⟨z, hz, hlarge⟩ := hg
    by_contra h
    have hsmall : ∀ i, ‖(gaussianPolynomial N g).derivative.derivative.eval (zgrid i)‖ ≤
        secondDerivativeEnvelope N K / 2 := by
      intro i
      exact (lt_of_not_ge (fun hi => h (Set.mem_iUnion.mpr ⟨i, hi⟩))).le
    have hdisk := polynomial_disk_bound_of_boundary_grid
      (gaussianPolynomial N g).derivative.derivative hR
      (by positivity : 0 ≤ 2 * Real.exp (K + 1) * (N : ℝ) ^ 5) hJ
      (fun w hw => gaussian_third_derivative_bound (by omega) g hcoeff hK hw) hsmall hz
    have herr := gaussian_second_derivative_grid_error_le hN hK hKN
    linarith
  have hA : (gaussianCoefficientMeasure (N + 1)).real A ≤ 1 / (N : ℝ) ^ 10 := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (N ^ 4))))
      (fun i _ => gaussian_second_derivative_point_tail hN hK (hgrid i))
    have hsum' : (∑ i : Fin (N ^ 4), (gaussianCoefficientMeasure (N + 1)).real
        {g | secondDerivativeEnvelope N K / 2 ≤
          ‖(gaussianPolynomial N g).derivative.derivative.eval (zgrid i)‖}) ≤
        (N : ℝ) ^ 4 * (4 / (N : ℝ) ^ 100) := by simpa using hsum
    apply ((measureReal_iUnion_fintype_le _).trans hsum').trans
    have hpow : (4 : ℝ) ≤ (N : ℝ) ^ 86 := by
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      exact (by norm_num : (4 : ℝ) ≤ 2 ^ 86).trans (pow_le_pow_left₀ (by norm_num) hN2 _)
    calc
      _ = (4 / (N : ℝ) ^ 86) * (1 / (N : ℝ) ^ 10) := by field_simp
      _ ≤ 1 * (1 / (N : ℝ) ^ 10) := by
        gcongr
        exact (div_le_one₀ (pow_pos hN0 _)).mpr hpow
      _ = _ := one_mul _
  have hE := gaussian_coefficient_truncation (N + 1) hN0.le
  exact ((measureReal_mono (μ := gaussianCoefficientMeasure (N + 1)) hsub).trans
    (measureReal_union_le A E)).trans (add_le_add hA (by simpa only [Nat.cast_add, Nat.cast_one] using hE))

end Erdos522
