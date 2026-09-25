/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianCoefficients
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Rotation-invariant Gaussian sums

A complex linear combination of independent standard circular Gaussians is
standard circular Gaussian whenever the sum of squared coefficient moduli is one.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- A complex linear combination of complex coefficients. -/
def complexCoefficientSum {n : ℕ} (a : Fin n → ℂ) (ω : Fin n → ℂ) : ℂ := ∑ k, a k * ω k

@[fun_prop]
theorem measurable_complexCoefficientSum {n : ℕ} (a : Fin n → ℂ) :
    Measurable (complexCoefficientSum a) := by unfold complexCoefficientSum; fun_prop

/-- Multiplication by a complex scalar acts on real dual vectors by conjugate multiplication. -/
theorem inner_complex_mul (a z t : ℂ) : inner ℝ (a * z) t = inner ℝ z (star a * t) := by
  simp [Complex.mul_re, Complex.mul_im, mul_add, add_mul]
  ring

/-- The characteristic function after multiplication by a fixed complex scalar. -/
theorem charFun_circularComplexGaussian_mul (a t : ℂ) :
    charFun (circularComplexGaussian.map (fun z => a * z)) t =
      Complex.exp (-(‖a‖ ^ 2 * ‖t‖ ^ 2 : ℝ) / 4) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_complex_mul]
  change charFun circularComplexGaussian (star a * t) = _
  rw [charFun_circularComplexGaussian, norm_mul, norm_star, mul_pow]

/-- Every normalized finite complex coefficient sum has the same circular Gaussian law. -/
theorem map_complexCoefficientSum_circularGaussian {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    (Measure.pi (fun _ : Fin n => circularComplexGaussian)).map (complexCoefficientSum a) =
      circularComplexGaussian := by
  let μ := Measure.pi (fun _ : Fin n => circularComplexGaussian)
  let X := fun k (ω : Fin n → ℂ) => a k * ω k
  have hind : iIndepFun X μ := iIndepFun_pi (fun _ => by fun_prop)
  have hmap (k : Fin n) : μ.map (X k) = circularComplexGaussian.map (fun z => a k * z) := by
    have heval := measurePreserving_eval (fun _ : Fin n => circularComplexGaussian) k
    rw [← heval.map_eq, Measure.map_map (by fun_prop) heval.measurable]
    rfl
  apply Measure.ext_of_charFun
  ext t
  have hcf := congrFun (hind.charFun_map_fun_sum_eq_prod (fun _ => by fun_prop)) t
  change charFun (μ.map (fun ω => ∑ k, X k ω)) t = _
  rw [hcf]
  simp only [Finset.prod_apply, hmap, charFun_circularComplexGaussian_mul,
    charFun_circularComplexGaussian]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Complex.ofReal_sum,
    ← Finset.sum_mul, ha, one_mul]

end Erdos522
