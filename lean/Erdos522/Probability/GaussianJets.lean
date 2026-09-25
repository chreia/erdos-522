/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianFourierLogarithmicMoments
import Erdos522.Probability.GaussianApproximation.PairedSmallBall

/-!
# Exact Gaussian laws for polynomial jets

Finite sums of real Gaussian coefficients have exactly the Gaussian law with
coefficient Gram covariance. Polynomial evaluation identifies these vector
sums with normalized value-derivative jets at one or two points.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Matrix WithLp
open scoped BigOperators RealInnerProductSpace NNReal
namespace Erdos522

/-- A vector-valued linear combination of independent real Gaussian coefficients. -/
def gaussianVectorSum {n d : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : Fin n → ℝ) : EuclideanSpace ℝ (Fin d) := ∑ k, g k • a k

@[fun_prop]
theorem measurable_gaussianVectorSum {n d : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    Measurable (gaussianVectorSum a) := by
  unfold gaussianVectorSum
  fun_prop

theorem inner_gaussianVectorSum {n d : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (g : Fin n → ℝ) :
    ⟪gaussianVectorSum a g, x⟫ = realGaussianSum (fun k => ⟪x, a k⟫) g := by
  simp only [gaussianVectorSum, realGaussianSum, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_comm]
  ring

/-- Gaussian coefficients produce exactly the coefficient Gram Gaussian law. -/
theorem map_gaussianVectorSum {N d : ℕ} (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d)) :
    (gaussianCoefficientMeasure (N + 1)).map (gaussianVectorSum a) =
      multivariateGaussian 0 (signCovarianceMatrix a) := by
  apply Measure.ext_of_charFun
  ext x
  rw [charFun_map_eq_charFun_map_inner_one (measurable_gaussianVectorSum a).aemeasurable]
  simp_rw [inner_gaussianVectorSum]
  have hS : (signCovarianceMatrix a).PosSemidef := covarianceMatrix_posSemidef _
  rw [map_realGaussianSum, charFun_gaussianReal,
    charFun_multivariateGaussian hS, signCovarianceMatrix_form]
  simp only [Real.coe_toNNReal _ (Finset.sum_nonneg fun k _ => sq_nonneg _),
    inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  congr 1
  simp [pow_two]

/-- The polynomial radial derivative is the coefficient sum weighted by the index. -/
theorem gaussianPolynomial_radial_derivative (N : ℕ) (g : Fin (N + 1) → ℝ) (w : ℂ) :
    w * (gaussianPolynomial N g).derivative.eval w = ∑ k, (k.val : ℂ) * (g k : ℂ) * w ^ k.val := by
  simp only [gaussianPolynomial, derivative_sum, derivative_monomial,
    eval_finsetSum, eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases hk : k.val with
  | zero => simp
  | succ j => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- Evaluation is the finite Gaussian coefficient sum. -/
theorem gaussianPolynomial_eval (N : ℕ) (g : Fin (N + 1) → ℝ) (w : ℂ) :
    (gaussianPolynomial N g).eval w = ∑ k, (g k : ℂ) * w ^ k.val := by
  simp only [gaussianPolynomial, eval_finsetSum, eval_monomial]

/-- The four Gaussian coordinates are exactly the polynomial value and radial derivative. -/
theorem gaussianVectorSum_realJetCoefficient (N : ℕ) (r : ℝ) (z : ℂ)
    (g : Fin (N + 1) → ℝ) :
    gaussianVectorSum (realJetCoefficient N r z) g =
      normalizedPolynomialJet (gaussianPolynomial N g) N (r * z) := by
  ext i
  fin_cases i <;>
    simp only [gaussianVectorSum, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      smul_eq_mul, realJetCoefficient, normalizedPolynomialJet, gaussianPolynomial_radial_derivative,
      gaussianPolynomial_eval,
      Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num
    ring

/-- Two Gaussian jets use the same finite Gaussian coefficient sequence. -/
theorem gaussianVectorSum_realPairedJetCoefficient (N : ℕ) (r s : ℝ) (z w : ℂ)
    (g : Fin (N + 1) → ℝ) :
    gaussianVectorSum (realPairedJetCoefficient N r s z w) g =
      normalizedPolynomialJetPair (gaussianPolynomial N g) N (r * z) (s * w) := by
  ext i
  fin_cases i <;>
    simp only [gaussianVectorSum, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      smul_eq_mul, realPairedJetCoefficient, normalizedPolynomialJetPair,
      gaussianPolynomial_radial_derivative, gaussianPolynomial_eval,
      Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num
    ring

/-- The normalized Gaussian polynomial jet has the exact four-dimensional law. -/
theorem map_normalizedGaussianPolynomialJet (N : ℕ) (r : ℝ) (z : ℂ) :
    (gaussianCoefficientMeasure (N + 1)).map
      (fun g => normalizedPolynomialJet (gaussianPolynomial N g) N (r * z)) =
      multivariateGaussian 0 (signCovarianceMatrix (realJetCoefficient N r z)) := by
  simp_rw [← gaussianVectorSum_realJetCoefficient]
  exact map_gaussianVectorSum (realJetCoefficient N r z)

/-- The pair of normalized jets has the exact eight-dimensional Gaussian law. -/
theorem map_normalizedGaussianPolynomialJetPair (N : ℕ) (r s : ℝ) (z w : ℂ) :
    (gaussianCoefficientMeasure (N + 1)).map
      (fun g => normalizedPolynomialJetPair (gaussianPolynomial N g) N (r * z) (s * w)) =
      multivariateGaussian 0 (signCovarianceMatrix (realPairedJetCoefficient N r s z w)) := by
  simp_rw [← gaussianVectorSum_realPairedJetCoefficient]
  exact map_gaussianVectorSum (realPairedJetCoefficient N r s z w)

end Erdos522
