/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherCoordinates
import SLT.HansonWright

/-!
# Moments of finite Rademacher sums

The product sign law gives coefficient-uniform moment bounds. Real linear
combinations satisfy the Gaussian moment-generating-function bound; decomposing
a complex sum into its real and imaginary parts gives the complex inequality.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- Real Rademacher sums have the sum of squared coefficients as variance proxy. -/
theorem hasSubgaussianMGF_sign_sum {N : ℕ} (a : Fin (N + 1) → ℝ) :
    HasSubgaussianMGF (fun ω : SignVector N => ∑ k, a k * realSign (ω k))
      (∑ k, NNReal.mk ((a k) ^ 2) (sq_nonneg _)) (signMeasure N) := by
  apply HasSubgaussianMGF.sum_of_iIndepFun
  · exact (iIndepFun_realSign N).comp (fun k x => a k * x) (by fun_prop)
  · intro k _
    convert! (hasSubgaussianMGF_coordinate k).const_mul (a k) using 1
    change NNReal.mk ((a k) ^ 2) _ = NNReal.mk ((a k) ^ 2) _ * 1
    rw [mul_one]

/-- An explicit even-moment bound with an arbitrary positive upper bound for
    the coefficient energy. -/
theorem integral_even_pow_sign_sum_le {N : ℕ} (a : Fin (N + 1) → ℝ)
    {V : ℝ} (hV : 0 < V) (ha : ∑ k, (a k) ^ 2 ≤ V) (m : ℕ) :
    (∫ ω : SignVector N, (∑ k, a k * realSign (ω k)) ^ (2 * m) ∂signMeasure N) ≤
      (Nat.factorial m : ℝ) * Real.exp 1 * (V * Real.exp 1) ^ m := by
  have h := HansonWright.integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le
    (hasSubgaussianMGF_sign_sum a) (θ := 1) (C0 := V) (by norm_num) hV
    (by simpa only [NNReal.coe_sum, NNReal.coe_mk] using ha) m
  simp only [one_pow, one_mul, integral_div] at h
  have hf : (0 : ℝ) < Nat.factorial m := by positivity
  calc
    _ ≤ (Real.exp 1 * (V * Real.exp 1) ^ m) * (Nat.factorial m : ℝ) :=
      (div_le_iff₀ hf).mp h
    _ = _ := by ring

/-- A complex linear combination of the coordinate signs. -/
def complexSignSum {N : ℕ} (a : Fin (N + 1) → ℂ) (ω : SignVector N) : ℂ :=
  ∑ k, sign (ω k) * a k

@[simp] theorem re_complexSignSum {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    (complexSignSum a ω).re = ∑ k, (a k).re * realSign (ω k) := by
  simp only [complexSignSum, ← ofReal_realSign, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm]

@[simp] theorem im_complexSignSum {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    (complexSignSum a ω).im = ∑ k, (a k).im * realSign (ω k) := by
  simp only [complexSignSum, ← ofReal_realSign, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, mul_comm]

/-- Even moments of a complex sum, with the coefficient energy kept explicit. -/
theorem integral_even_norm_complexSignSum_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, ‖complexSignSum a ω‖ ^ (2 * m) ∂signMeasure N) ≤
      2 ^ m * (Nat.factorial m : ℝ) * Real.exp 1 * (V * Real.exp 1) ^ m := by
  have hre : ∑ k, (a k).re ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).im])).trans ha
  have him : ∑ k, (a k).im ^ 2 ≤ V := (Finset.sum_le_sum (fun k _ =>
    by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (a k).re])).trans ha
  have hreal := integral_even_pow_sign_sum_le (fun k => (a k).re) hV hre m
  have himag := integral_even_pow_sign_sum_le (fun k => (a k).im) hV him m
  have hpoint (ω : SignVector N) :
      ‖complexSignSum a ω‖ ^ (2 * m) ≤ 2 ^ (m - 1) *
        ((complexSignSum a ω).re ^ (2 * m) + (complexSignSum a ω).im ^ (2 * m)) := by
    rw [pow_mul, Complex.sq_norm, Complex.normSq_apply]
    simpa only [pow_mul, pow_two] using
      add_pow_le (sq_nonneg (complexSignSum a ω).re)
        (sq_nonneg (complexSignSum a ω).im) m
  have htwo : (2 : ℝ) ^ (m - 1) * 2 = 2 ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  calc
    _ ≤ ∫ ω, 2 ^ (m - 1) *
        ((complexSignSum a ω).re ^ (2 * m) + (complexSignSum a ω).im ^ (2 * m))
        ∂signMeasure N := integral_mono Integrable.of_finite Integrable.of_finite hpoint
    _ = 2 ^ (m - 1) *
        ((∫ ω, (∑ k, (a k).re * realSign (ω k)) ^ (2 * m) ∂signMeasure N) +
          ∫ ω, (∑ k, (a k).im * realSign (ω k)) ^ (2 * m) ∂signMeasure N) := by
      rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite]
      simp only [re_complexSignSum, im_complexSignSum]
    _ ≤ 2 ^ (m - 1) * (2 *
        ((Nat.factorial m : ℝ) * Real.exp 1 * (V * Real.exp 1) ^ m)) := by
      gcongr
      linarith
    _ = _ := by rw [← mul_assoc, htwo]; ring

/-- The fourth moment is at most `8 exp(3)` times the squared coefficient energy. -/
theorem integral_fourth_norm_complexSignSum_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) :
    (∫ ω, ‖complexSignSum a ω‖ ^ 4 ∂signMeasure N) ≤
      8 * Real.exp 3 * V ^ 2 := by
  have h := integral_even_norm_complexSignSum_le a hV ha 2 (by norm_num)
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow] at h
  convert h using 1
  rw [show (3 : ℝ) = 1 + (1 + 1) by norm_num, Real.exp_add, Real.exp_add]
  ring

/-- The usual polynomial growth in the moment order in the complex
    Khintchine inequality, with an explicit numerical constant. -/
theorem integral_even_norm_complexSignSum_le_pow {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, ‖complexSignSum a ω‖ ^ (2 * m) ∂signMeasure N) ≤
      (2 * Real.exp 2 * (m : ℝ) * V) ^ m := by
  have hf : (Nat.factorial m : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have he : Real.exp 1 ≤ Real.exp 1 ^ m := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) hm
  calc
    _ ≤ 2 ^ m * (Nat.factorial m : ℝ) * Real.exp 1 * (V * Real.exp 1) ^ m :=
      integral_even_norm_complexSignSum_le a hV ha m hm
    _ ≤ 2 ^ m * (m : ℝ) ^ m * Real.exp 1 ^ m * (V * Real.exp 1) ^ m := by
      gcongr
    _ = _ := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      simp only [mul_pow]
      ring

/-- All finite moments of the joint sign-and-angle polynomial are integrable. -/
theorem integrable_pow_norm_randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ) (p : ℕ) :
    Integrable (fun q => ‖randomFourier a q‖ ^ p) (fourierMeasure N) := by
  apply (integrable_prod_iff
    ((measurable_randomFourier a).norm.pow_const p).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun ω =>
      ((continuous_fourierPolynomial a ω).norm.pow p).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · exact Integrable.of_finite

/-- Multiplying each coefficient by its Fourier phase identifies angular
    evaluation with a complex Rademacher sum. -/
theorem fourierPolynomial_eq_complexSignSum {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) (θ : AddCircle (1 : ℝ)) :
    fourierPolynomial a ω θ = complexSignSum (fun k => a k * fourier k.val θ) ω := by
  simp only [fourierPolynomial_eq_sum, complexSignSum, mul_assoc]

/-- Fourier phases preserve coefficient energy. -/
theorem sum_sq_norm_fourier_coefficients {N : ℕ} (a : Fin (N + 1) → ℂ)
    (θ : AddCircle (1 : ℝ)) :
    ∑ k, ‖a k * fourier k.val θ‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- The coefficient-uniform Khintchine estimate under the joint sign-and-angle law. -/
theorem integral_even_norm_randomFourier_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) (m : ℕ) (hm : 1 ≤ m) :
    (∫ q, ‖randomFourier a q‖ ^ (2 * m) ∂fourierMeasure N) ≤
      (2 * Real.exp 2 * (m : ℝ) * V) ^ m := by
  have hi := integrable_pow_norm_randomFourier a (2 * m)
  rw [fourierMeasure, integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _θ : AddCircle (1 : ℝ), (2 * Real.exp 2 * (m : ℝ) * V) ^ m
        ∂AddCircle.haarAddCircle := by
      apply integral_mono hi.integral_prod_right (integrable_const _)
      intro θ
      simp only [randomFourier, fourierPolynomial_eq_complexSignSum]
      exact integral_even_norm_complexSignSum_le_pow
        (fun k => a k * fourier k.val θ) hV
        (by rwa [sum_sq_norm_fourier_coefficients]) m hm
    _ = _ := by simp

/-- A uniform fourth moment on the product of the sign space and the circle. -/
theorem integral_fourth_norm_randomFourier_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V) :
    (∫ q, ‖randomFourier a q‖ ^ 4 ∂fourierMeasure N) ≤
      8 * Real.exp 3 * V ^ 2 := by
  have hi := integrable_pow_norm_randomFourier a 4
  rw [fourierMeasure, integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _θ : AddCircle (1 : ℝ), 8 * Real.exp 3 * V ^ 2
        ∂AddCircle.haarAddCircle := by
      apply integral_mono hi.integral_prod_right (integrable_const _)
      intro θ
      simp only [randomFourier, fourierPolynomial_eq_complexSignSum]
      exact integral_fourth_norm_complexSignSum_le
        (fun k => a k * fourier k.val θ) hV
        (by rwa [sum_sq_norm_fourier_coefficients])
    _ = _ := by simp

end Erdos522.LogMoments
