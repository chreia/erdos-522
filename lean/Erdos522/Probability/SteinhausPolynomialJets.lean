/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.CircularJetSmallBall
import Erdos522.Probability.Covariance.CircularPairedJets

/-!
# Polynomial jets with circular coefficients

Real and imaginary coefficient coordinates identify the circular vector jet
with polynomial evaluation and the radial derivative. This gives joint
small-ball estimates directly on the finite Steinhaus coefficient space.
-/

noncomputable section
open MeasureTheory Polynomial WithLp
open scoped BigOperators
namespace Erdos522

/-- The radial derivative of a coefficient-vector polynomial weights each
coefficient by its index. -/
theorem ofFn_radial_derivative (N : ℕ) (a : Fin (N + 1) → ℂ) (w : ℂ) :
    w * (Polynomial.ofFn (N + 1) a).derivative.eval w =
      ∑ k, (k.val : ℂ) * a k * w ^ k.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [derivative_sum, derivative_monomial, eval_finsetSum,
    eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases hk : k.val with
  | zero => simp
  | succ j => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- The circular jet is exactly the normalized polynomial value and radial
derivative, for every complex coefficient vector. -/
theorem circularJet_eq_normalizedPolynomialJet (N : ℕ) (r : ℝ) (z : ℂ)
    (a : Fin (N + 1) → ℂ) :
    circularJet N r z a =
      normalizedPolynomialJet (Polynomial.ofFn (N + 1) a) N (r * z) := by
  have heval (w : ℂ) : (Polynomial.ofFn (N + 1) a).eval w =
      ∑ k, a k * w ^ k.val := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    simp only [eval_finsetSum, eval_monomial]
  ext i
  fin_cases i <;>
    simp only [circularJet, circularVectorSum, circularVector, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      realJetCoefficient, imaginaryJetCoefficient, normalizedPolynomialJet,
      ofFn_radial_derivative, heval, Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, add_zero]
    norm_num
    ring

/-- Two circular jets use exactly the same polynomial coefficients. -/
theorem circularPairedJet_eq_normalizedPolynomialJetPair (N : ℕ) (r s : ℝ)
    (z w : ℂ) (a : Fin (N + 1) → ℂ) :
    circularPairedJet N r s z w a =
      normalizedPolynomialJetPair (Polynomial.ofFn (N + 1) a) N (r * z) (s * w) := by
  have heval (v : ℂ) : (Polynomial.ofFn (N + 1) a).eval v =
      ∑ k, a k * v ^ k.val := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    simp only [eval_finsetSum, eval_monomial]
  ext i
  fin_cases i <;>
    simp only [circularPairedJet, circularVectorSum, circularVector, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      imaginaryPairedJetCoefficient, realPairedJetCoefficient, normalizedPolynomialJetPair,
      ofFn_radial_derivative, heval, Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, add_zero]
    norm_num
    ring

@[fun_prop]
theorem measurable_circularPairedJet (N : ℕ) (r s : ℝ) (z w : ℂ) :
    Measurable (circularPairedJet N r s z w) := by
  unfold circularPairedJet circularVectorSum circularVector
  fun_prop

@[fun_prop]
theorem measurable_circularJet (N : ℕ) (r : ℝ) (z : ℂ) :
    Measurable (circularJet N r z) := by
  unfold circularJet circularVectorSum circularVector
  fun_prop

/-- Membership in the jet ball uses the exact square-root and radial
derivative normalizations. -/
theorem normalizedPolynomialJet_mem_jetSmallBallSet (P : ℂ[X]) (N : ℕ)
    (hN : 0 < N) (w : ℂ) (u v : ℝ) :
    normalizedPolynomialJet P N w ∈ jetSmallBallSet u v ↔
      ‖P.eval w‖ ≤ u * Real.sqrt N ∧
      ‖w * P.derivative.eval w‖ ≤ v * ((N : ℝ) * Real.sqrt N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  simp only [jetSmallBallSet, Set.mem_preimage, jetComplexCoordinates_normalizedPolynomialJet,
    Set.mem_prod, Metric.mem_closedBall, dist_zero_right, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos (mul_pos hn hs),
    div_le_iff₀ hs, div_le_iff₀ (mul_pos hn hs)]

/-- A Steinhaus polynomial has the annular joint small-ball bound at every
angle, with the four-dimensional Gaussian approximation error. -/
theorem exists_steinhaus_polynomial_jet_small_ball_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (z : ℂ) (_ : ‖z‖ = 1) (u v : ℝ) (_ : 0 ≤ u) (_ : 0 ≤ v),
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {a |
        ‖(Polynomial.ofFn (N + 1) a).eval (r * z)‖ ≤ u * Real.sqrt N ∧
        ‖(r * z) * (Polynomial.ofFn (N + 1) a).derivative.eval (r * z)‖ ≤
          v * ((N : ℝ) * Real.sqrt N)} ≤
        u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 32) ^ 2) +
          circularJetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, hbound⟩ := exists_annular_circular_jet_small_ball_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru z hz u v hu hv
  have hb := hbound N hN K r hK hNK hrl hru z hz u v hu hv
  rw [measureReal_def, Measure.map_apply (measurable_circularJet N r z)
    (measurableSet_jetSmallBallSet u v)] at hb
  have he : circularJet N r z ⁻¹' jetSmallBallSet u v = {a |
      ‖(Polynomial.ofFn (N + 1) a).eval (r * z)‖ ≤ u * Real.sqrt N ∧
      ‖(r * z) * (Polynomial.ofFn (N + 1) a).derivative.eval (r * z)‖ ≤
        v * ((N : ℝ) * Real.sqrt N)} := by
    ext a
    rw [Set.mem_preimage, circularJet_eq_normalizedPolynomialJet,
      normalizedPolynomialJet_mem_jetSmallBallSet _ N hN]
    rfl
  rw [he] at hb
  exact hb

end Erdos522
