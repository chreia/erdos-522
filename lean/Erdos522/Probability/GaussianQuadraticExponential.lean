/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianCoefficients
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential moments of Gaussian squares

The exact Gaussian integral yields the moment-generating function of a
standard Gaussian square.  Its centered logarithm is bounded quadratically
on the interval needed for weighted-energy concentration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Erdos522

private theorem gaussian_square_density_identity (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The exponential of a standard Gaussian square is integrable below its critical parameter. -/
theorem integrable_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussian_square_density_identity]
  exact (integrable_exp_neg_mul_sq (by linarith : 0 < 1 / 2 - t)).const_mul _

/-- The exact moment-generating function of a standard Gaussian square. -/
theorem integral_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_square_density_identity]
  rw [integral_const_mul, integral_gaussian]
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht' : 0 < 1 / 2 - t := by linarith
  have he : Real.pi / (1 / 2 - t) = (2 * Real.pi) / (1 - 2 * t) := by
    field_simp
  rw [he, Real.sqrt_div (by positivity), inv_mul_eq_div,
    div_div, mul_comm (Real.sqrt (1 - 2 * t))]
  field_simp

/-- The centered Gaussian square cumulant has a quadratic upper bound. -/
theorem neg_half_log_one_sub_two_mul_le {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 4) :
    -(1 / 2 : ℝ) * Real.log (1 - 2 * s) ≤ s + 2 * s ^ 2 := by
  let f : ℝ → ℝ := fun x => x + 2 * x ^ 2 + (1 / 2 : ℝ) * Real.log (1 - 2 * x)
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 4)) :
      HasDerivAt f (2 * x * (1 - 4 * x) / (1 - 2 * x)) x := by
    have hx0 : 1 - 2 * x ≠ 0 := by linarith [hx.2]
    have h := ((hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).const_mul 2)).add
      ((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)).log hx0).const_mul
        (1 / 2 : ℝ))
    simp only [Pi.add_def, Pi.sub_def, Pi.pow_def, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_one, zero_sub] at h
    convert h using 1
    field_simp
    ring
  have hm : MonotoneOn f (Icc (0 : ℝ) (1 / 4)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx'.1)
        (by linarith [hx'.2])) (by linarith [hx'.2])
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 4)) ⟨hs, hs'⟩ hs
  dsimp [f] at h
  simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero,
    Real.log_one] at h
  linarith

/-- A scalar Gaussian exponential moment is bounded by its mean and a quadratic remainder. -/
theorem integral_exp_mul_sq_gaussianReal_le {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 4) :
    (∫ x : ℝ, Real.exp (s * x ^ 2) ∂gaussianReal 0 1) ≤ Real.exp (s + 2 * s ^ 2) := by
  rw [integral_exp_mul_sq_gaussianReal (by linarith : s < 1 / 2)]
  have hpos : 0 < 1 - 2 * s := by linarith
  have he : (Real.sqrt (1 - 2 * s))⁻¹ = Real.exp (-(1 / 2 : ℝ) * Real.log (1 - 2 * s)) := by
    rw [← Real.exp_log (by positivity : 0 < (Real.sqrt (1 - 2 * s))⁻¹),
      Real.log_inv, Real.log_sqrt hpos.le]
    congr 1
    ring
  rw [he]
  exact Real.exp_le_exp.mpr (neg_half_log_one_sub_two_mul_le hs hs')

end Erdos522
