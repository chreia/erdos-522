/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BoundedComplexHoeffding
import Erdos522.Probability.DerivativeSupremum
import Erdos522.Probability.TailSupremum

/-!
# Suprema for bounded complex-coefficient polynomials

The same deterministic boundary grids control independent mean-zero complex
coefficients. The coefficient bound multiplies the derivative and tail
envelopes; the finite failure probabilities remain unchanged.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522
namespace BoundedPolynomialSuprema

/-- Iterated derivatives of a coefficient-vector polynomial use the same
deterministic differentiated coefficients as the sign model. -/
theorem eval_iterate_derivative_ofFn (N m : ℕ) (a : Fin (N + 1) → ℂ) (z : ℂ) :
    (Polynomial.derivative^[m] (Polynomial.ofFn (N + 1) a)).eval z =
      ∑ k, DerivativeSupremum.derivativeCoefficient N m z k * a k := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [← C_mul_X_pow_eq_monomial, iterate_derivative_sum,
    iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    DerivativeSupremum.derivativeCoefficient]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Deterministic disk control for bounded complex coefficients. -/
theorem norm_iterate_derivative_ofFn_le (N m : ℕ) (a : Fin (N + 1) → ℂ)
    {B R : ℝ} (_hB : 0 ≤ B) (ha : ∀ k, ‖a k‖ ≤ B) (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(Polynomial.derivative^[m] (Polynomial.ofFn (N + 1) a)).eval z‖ ≤
      B * ((N + 1 : ℝ) * ((N : ℝ) ^ m * R ^ N)) := by
  rw [eval_iterate_derivative_ofFn]
  calc
    _ ≤ ∑ k, ‖DerivativeSupremum.derivativeCoefficient N m z k * a k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin (N + 1), ((N : ℝ) ^ m * R ^ N) * B := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (DerivativeSupremum.norm_derivativeCoefficient_le N m hR hz k)
        (ha k) (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

/-- Simultaneous bounds on all coordinates hold on the actual product law. -/
theorem ae_coordinate_norm_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)] {B : ℝ}
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) :
    ∀ᵐ a ∂Measure.pi μ, ∀ k, ‖a k‖ ≤ B := by
  apply ae_all_iff.mpr
  intro k
  exact (measurePreserving_eval μ k).quasiMeasurePreserving.ae (hbound k)

/-- Boundary samples control a polynomial family in probability, even when
the deterministic derivative bound holds only almost surely. -/
theorem measure_polynomial_disk_supremum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ι → Ω → Polynomial ℂ)
    {R M t A p : ℝ} {J : ℕ} (hR : 0 < R) (hM : 0 ≤ M) (hJ : 0 < J)
    (hderiv : ∀ᵐ ω ∂μ, ∀ i z, ‖z‖ ≤ R → ‖(P i ω).derivative.eval z‖ ≤ M)
    (hpoint : ∀ i j, μ.real {ω | t ≤ ‖(P i ω).eval (polynomialBoundaryGrid R J j)‖} ≤ p)
    (herror : t + M * (2 * Real.pi * R / J) ≤ A) :
    μ.real {ω | ∃ i z, ‖z‖ ≤ R ∧ A < ‖(P i ω).eval z‖} ≤
      (Fintype.card ι : ℝ) * J * p := by
  have hsub : {ω | ∃ i z, ‖z‖ ≤ R ∧ A < ‖(P i ω).eval z‖} ≤ᵐ[μ]
      ⋃ ij : ι × Fin J, {ω | t ≤ ‖(P ij.1 ω).eval (polynomialBoundaryGrid R J ij.2)‖} := by
    filter_upwards [hderiv] with ω hω
    intro ⟨i, z, hz, hlarge⟩
    by_contra h
    have hsmall (j : Fin J) : ‖(P i ω).eval (polynomialBoundaryGrid R J j)‖ ≤ t := by
      by_contra! hj
      exact h (Set.mem_iUnion.mpr ⟨(i, j), hj.le⟩)
    have hb := polynomial_disk_bound_of_boundary_grid (P i ω) hR hM hJ (hω i) hsmall hz
    linarith
  have hp := (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    (measureReal_iUnion_fintype_le _)
  apply hp.trans
  simpa [Fintype.card_prod, Nat.cast_mul, mul_assoc] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (ι × Fin J))) (fun ij _ => hpoint ij.1 ij.2)

/-- A strict interpolation margin also controls the closed supremum event. -/
theorem measure_polynomial_disk_supremum_ge_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ι → Ω → Polynomial ℂ)
    {R M t A p : ℝ} {J : ℕ} (hR : 0 < R) (hM : 0 ≤ M) (hJ : 0 < J)
    (hderiv : ∀ᵐ ω ∂μ, ∀ i z, ‖z‖ ≤ R → ‖(P i ω).derivative.eval z‖ ≤ M)
    (hpoint : ∀ i j, μ.real {ω | t ≤ ‖(P i ω).eval (polynomialBoundaryGrid R J j)‖} ≤ p)
    (herror : t + M * (2 * Real.pi * R / J) < A) :
    μ.real {ω | ∃ i z, ‖z‖ ≤ R ∧ A ≤ ‖(P i ω).eval z‖} ≤
      (Fintype.card ι : ℝ) * J * p := by
  have hsub : {ω | ∃ i z, ‖z‖ ≤ R ∧ A ≤ ‖(P i ω).eval z‖} ≤ᵐ[μ]
      ⋃ ij : ι × Fin J, {ω | t ≤ ‖(P ij.1 ω).eval (polynomialBoundaryGrid R J ij.2)‖} := by
    filter_upwards [hderiv] with ω hω
    intro ⟨i, z, hz, hlarge⟩
    by_contra h
    have hsmall (j : Fin J) : ‖(P i ω).eval (polynomialBoundaryGrid R J j)‖ ≤ t := by
      by_contra! hj
      exact h (Set.mem_iUnion.mpr ⟨(i, j), hj.le⟩)
    have hb := polynomial_disk_bound_of_boundary_grid (P i ω) hR hM hJ (hω i) hsmall hz
    linarith
  have hp := (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    (measureReal_iUnion_fintype_le _)
  apply hp.trans
  simpa [Fintype.card_prod, Nat.cast_mul, mul_assoc] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (ι × Fin J))) (fun ij _ => hpoint ij.1 ij.2)

/-- The enlarged-disk third-derivative bound acquires exactly one factor `B`. -/
theorem third_derivative_bound {N : ℕ} (hN : 1 ≤ N) (a : Fin (N + 1) → ℂ)
    {B K : ℝ} (hB : 0 ≤ B) (ha : ∀ k, ‖a k‖ ≤ B) (hK : 0 ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
    ‖(Polynomial.ofFn (N + 1) a).derivative.derivative.derivative.eval z‖ ≤
      B * (2 * Real.exp (K + 1) * (N : ℝ) ^ 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase := norm_iterate_derivative_ofFn_le N 3 a hB ha
    (by linarith [div_nonneg (by linarith : 0 ≤ K + 1) hN0.le] : 1 ≤ 1 + (K + 1) / N) hz
  change ‖(Polynomial.ofFn (N + 1) a).derivative.derivative.derivative.eval z‖ ≤ _ at hbase
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ hB
  calc
    _ ≤ (2 * N) * ((N : ℝ) ^ 3 * Real.exp (K + 1)) := by
      gcongr
      · linarith
      · exact DerivativeSupremum.annular_radius_pow_le (by omega) hK
    _ = _ := by ring

/-- Scaling the envelope by the coefficient bound cancels its Hoeffding cost. -/
theorem measure_scaled_complex_sum_ge_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)] (a : ι → ℂ)
    {B V t : ℝ} (hB : 0 < B) (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0)
    (ht : 0 ≤ t) :
    (Measure.pi μ).real {ω | B * t ≤ ‖∑ k, a k * ω k‖} ≤
      4 * Real.exp (-t ^ 2 / (4 * V)) := by
  have h := measure_norm_bounded_complex_sum_ge_le μ a hB.le hV.le ha hbound hmean
    (mul_nonneg hB.le ht)
  convert h using 1
  congr 2
  field_simp

/-- Pointwise second-derivative tails retain the same inverse-power bound
after multiplying the envelope by `B`. -/
theorem second_derivative_point_tail {N : ℕ} (hN : 2 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    {B K : ℝ} (hB : 0 < B) (hK : 0 ≤ K)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0)
    {z : ℂ} (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
    (Measure.pi μ).real {a | B * (DerivativeSupremum.secondDerivativeEnvelope N K / 2) ≤
      ‖(Polynomial.ofFn (N + 1) a).derivative.derivative.eval z‖} ≤
        4 / (N : ℝ) ^ 100 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hV : 0 < 2 * Real.exp (2 * K + 2) * (N : ℝ) ^ 5 := by positivity
  change (Measure.pi μ).real {a | B * (DerivativeSupremum.secondDerivativeEnvelope N K / 2) ≤
      ‖(Polynomial.derivative^[2] (Polynomial.ofFn (N + 1) a)).eval z‖} ≤ _
  simp_rw [eval_iterate_derivative_ofFn]
  apply (measure_scaled_complex_sum_ge_le μ (DerivativeSupremum.derivativeCoefficient N 2 z)
    hB hV (DerivativeSupremum.second_derivative_energy_le (by omega) hK hz) hbound hmean
    (by unfold DerivativeSupremum.secondDerivativeEnvelope; positivity)).trans
  have hexp : Real.exp (2 * K + 2) ≤ Real.exp (K + 4) ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hproduct := mul_le_mul_of_nonneg_right hexp
    (mul_nonneg (pow_nonneg hN0.le 5) hlog)
  have hsquare : (DerivativeSupremum.secondDerivativeEnvelope N K / 2) ^ 2 =
      2500 * Real.exp (K + 4) ^ 2 * (N : ℝ) ^ 5 * Real.log N := by
    unfold DerivativeSupremum.secondDerivativeEnvelope
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hquot : 100 * Real.log N ≤ (DerivativeSupremum.secondDerivativeEnvelope N K / 2) ^ 2 /
      (4 * (2 * Real.exp (2 * K + 2) * (N : ℝ) ^ 5)) := by
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

/-- The actual second-derivative bound for independent bounded complex
coefficients, on the full closed enlarged disk. -/
theorem second_derivative_supremum (N : ℕ) (hN : 2 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    {B K : ℝ} (hB : 0 < B) (hK : 0 ≤ K) (hKN : K + 1 ≤ (N : ℝ))
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, z ∂μ k) = 0) :
    (Measure.pi μ).real {a | ∃ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N ∧
      B * DerivativeSupremum.secondDerivativeEnvelope N K <
        ‖(Polynomial.ofFn (N + 1) a).derivative.derivative.eval z‖} ≤
          1 / (N : ℝ) ^ 10 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR : 0 < 1 + (K + 1) / (N : ℝ) := by positivity
  have hd : ∀ᵐ a ∂Measure.pi μ, ∀ (_i : Unit) z, ‖z‖ ≤ 1 + (K + 1) / N →
      ‖(Polynomial.ofFn (N + 1) a).derivative.derivative.derivative.eval z‖ ≤
        B * (2 * Real.exp (K + 1) * (N : ℝ) ^ 4) := by
    filter_upwards [ae_coordinate_norm_le μ hbound] with a ha
    exact fun _ _ hz => third_derivative_bound (by omega) a hB.le ha hK hz
  have hp := measure_polynomial_disk_supremum_le (Measure.pi μ)
    (fun (_i : Unit) a => (Polynomial.ofFn (N + 1) a).derivative.derivative)
    hR (by positivity) (pow_pos (by omega : 0 < N) 3) hd
    (fun _i j => second_derivative_point_tail hN μ hB hK hbound hmean
      (by simp [abs_of_pos hR] : ‖polynomialBoundaryGrid (1 + (K + 1) / N) (N ^ 3) j‖ ≤ _))
    (show B * (DerivativeSupremum.secondDerivativeEnvelope N K / 2) +
      (B * (2 * Real.exp (K + 1) * (N : ℝ) ^ 4)) *
        (2 * Real.pi * (1 + (K + 1) / N) / (N ^ 3 : ℕ)) ≤
        B * DerivativeSupremum.secondDerivativeEnvelope N K from by
      have he := mul_le_mul_of_nonneg_left
        (DerivativeSupremum.second_derivative_grid_error_le hN hK hKN) hB.le
      nlinarith)
  simp only [exists_const, Fintype.card_unit, Nat.cast_one, one_mul, Nat.cast_pow] at hp
  apply hp.trans
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

end BoundedPolynomialSuprema
end Erdos522
