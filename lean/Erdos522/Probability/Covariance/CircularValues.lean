/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.NormalizedValues
import Erdos522.Probability.GaussianApproximation.CircularVectors

/-!
# Exact covariance of normalized circular polynomial values

A circular coefficient contributes equally to two orthogonal real
directions. Exact variance normalization therefore gives covariance one
half of the identity at every angle and every radius.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- The quarter turn of the real normalized value coefficient. -/
def imaginaryValueCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1)) :
    EuclideanSpace ℝ (Fin 2) :=
  let a := realValueCoefficient N r z k
  toLp 2 ![-a 1, a 0]

/-- The polynomial value with circular coefficients, divided by its exact
standard deviation. -/
def circularValue (N : ℕ) (r : ℝ) (z : ℂ) :
    (Fin (N + 1) → ℂ) → EuclideanSpace ℝ (Fin 2) :=
  circularVectorSum (realValueCoefficient N r z) (imaginaryValueCoefficient N r z)

theorem norm_imaginaryValueCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1)) :
    ‖imaginaryValueCoefficient N r z k‖ = ‖realValueCoefficient N r z k‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, imaginaryValueCoefficient,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq]
  ring

/-- The two orthogonal coefficient directions give a scalar bilinear form. -/
theorem circularValue_coefficient_form (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1))
    (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, realValueCoefficient N r z k⟫ * ⟪y, realValueCoefficient N r z k⟫ +
      ⟪x, imaginaryValueCoefficient N r z k⟫ * ⟪y, imaginaryValueCoefficient N r z k⟫ =
        ‖realValueCoefficient N r z k‖ ^ 2 * ⟪x, y⟫ := by
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_two, imaginaryValueCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The exact circular covariance form has no exceptional angular set. -/
theorem circularValue_covariance_form (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    x.ofLp ⬝ᵥ circularCovarianceMatrix (realValueCoefficient N r z)
      (imaginaryValueCoefficient N r z) *ᵥ y.ofLp = ⟪x, y⟫ / 2 := by
  rw [circularCovarianceMatrix_form]
  simp_rw [circularValue_coefficient_form]
  rw [← Finset.sum_div, ← Finset.sum_mul, sum_sq_norm_realValueCoefficient N r z hz, one_mul]

/-- The covariance matrix of the actual circular value law is exactly `I/2`. -/
theorem circularValue_covariance_eq (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    circularCovarianceMatrix (realValueCoefficient N r z) (imaginaryValueCoefficient N r z) =
      Matrix.diagonal (fun _ => (1 / 2 : ℝ)) := by
  ext i j
  have h := circularValue_covariance_form N r z hz
    (toLp 2 (Pi.single i 1)) (toLp 2 (Pi.single j 1))
  by_cases hij : i = j <;>
    simpa [dotProduct, Matrix.mulVec, PiLp.inner_apply, RCLike.inner_apply,
      Matrix.diagonal_apply, Pi.single_apply, eq_comm, hij] using h

/-- The vector value is the real and imaginary parts of the normalized
coefficient-vector polynomial. -/
theorem circularValue_eq_polynomial (N : ℕ) (r : ℝ) (z : ℂ) (a : Fin (N + 1) → ℂ) :
    circularValue N r z a = toLp 2 ![
      ((Polynomial.ofFn (N + 1) a).eval (r * z)).re / radialSigma N r,
      ((Polynomial.ofFn (N + 1) a).eval (r * z)).im / radialSigma N r] := by
  have heval (w : ℂ) : (Polynomial.ofFn (N + 1) a).eval w = ∑ k, a k * w ^ k.val := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  ext i
  fin_cases i <;>
    simp only [circularValue, circularVectorSum, circularVector, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      realValueCoefficient, imaginaryValueCoefficient, heval,
      Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    norm_num
    ring

@[fun_prop]
theorem continuous_circularValue (N : ℕ) (r : ℝ) :
    Continuous (fun p : ℂ × (Fin (N + 1) → ℂ) => circularValue N r p.1 p.2) := by
  unfold circularValue circularVectorSum circularVector imaginaryValueCoefficient realValueCoefficient
  fun_prop

@[fun_prop]
theorem measurable_circularValue (N : ℕ) (r : ℝ) (z : ℂ) :
    Measurable (circularValue N r z) := by
  have h := (continuous_circularValue N r).comp
    (continuous_const.prodMk continuous_id : Continuous (fun a : Fin (N + 1) → ℂ => (z, a)))
  exact h.measurable

end Erdos522
