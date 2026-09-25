/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.RademacherJets
import Erdos522.Basic.RademacherPolynomial

/-!
# Polynomial interpretation of normalized jets

The finite product-sign vector represents the polynomial value and its
radial derivative at the point `r z`. The derivative coordinate has the
normalization `N √N`, exactly `N^{3/2}` for positive degree.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Erdos522
open LogMoments

/-- The real value-derivative jet of a polynomial, normalized by `√N` and `N√N`. -/
def normalizedPolynomialJet (P : ℂ[X]) (N : ℕ) (w : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![(P.eval w).re / Real.sqrt N, (P.eval w).im / Real.sqrt N,
    (w * P.derivative.eval w).re / ((N : ℝ) * Real.sqrt N),
    (w * P.derivative.eval w).im / ((N : ℝ) * Real.sqrt N)]

/-- The finite sign vector is exactly the normalized polynomial value and radial derivative. -/
theorem realRademacherJet_eq_normalizedPolynomialJet (N : ℕ) (r : ℝ) (z : ℂ)
    (ω : SignVector N) :
    realRademacherJet N r z ω = normalizedPolynomialJet (rademacherPolynomial N ω) N (r * z) := by
  ext i
  fin_cases i <;>
    simp only [realRademacherJet, signVectorSum, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      realJetCoefficient, normalizedPolynomialJet, rademacherPolynomial_eval, rademacherPolynomial_radial_derivative,
      Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [← ofReal_realSign, mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num
    ring

/-- The derivative normalization `N√N` is the manuscript's real power `N^{3/2}`. -/
theorem degree_mul_sqrt_eq_three_halves (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * Real.sqrt N = (N : ℝ) ^ (3 / 2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (N : ℝ) * Real.sqrt N = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = (N : ℝ) ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hn _ _).symm
    _ = _ := by norm_num

/-- The eight real coordinates of the same polynomial jet at two points. -/
def normalizedPolynomialJetPair (P : ℂ[X]) (N : ℕ) (w₁ w₂ : ℂ) :
    EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 ![(P.eval w₁).re / Real.sqrt N, (P.eval w₁).im / Real.sqrt N,
    (w₁ * P.derivative.eval w₁).re / ((N : ℝ) * Real.sqrt N),
    (w₁ * P.derivative.eval w₁).im / ((N : ℝ) * Real.sqrt N),
    (P.eval w₂).re / Real.sqrt N, (P.eval w₂).im / Real.sqrt N,
    (w₂ * P.derivative.eval w₂).re / ((N : ℝ) * Real.sqrt N),
    (w₂ * P.derivative.eval w₂).im / ((N : ℝ) * Real.sqrt N)]

/-- The paired random vector consists of jets of one polynomial with one coefficient vector. -/
theorem realPairedRademacherJet_eq_normalizedPolynomialJetPair (N : ℕ) (r s : ℝ)
    (z w : ℂ) (ω : SignVector N) :
    realPairedRademacherJet N r s z w ω =
      normalizedPolynomialJetPair (rademacherPolynomial N ω) N (r * z) (s * w) := by
  ext i
  fin_cases i <;>
    simp only [realPairedRademacherJet, signVectorSum, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul, realPairedJetCoefficient, normalizedPolynomialJetPair,
      rademacherPolynomial_eval, rademacherPolynomial_radial_derivative,
      Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [← ofReal_realSign, mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num
    ring

end Erdos522
