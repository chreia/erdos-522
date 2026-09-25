/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Relative entropy of centered real Gaussian distributions

The covariance comparison formula begins with the logarithm of the ratio of
Gaussian densities. Positive variances give equivalent measures, so this
pointwise density calculation determines the log-likelihood ratio.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace Erdos522

/-- Centered Gaussian distributions with positive variances are equivalent. -/
theorem gaussianReal_absolutelyContinuous_gaussianReal {v w : ℝ≥0}
    (hv : v ≠ 0) (hw : w ≠ 0) : gaussianReal 0 v ≪ gaussianReal 0 w :=
  (gaussianReal_absolutelyContinuous 0 hv).trans
    (gaussianReal_absolutelyContinuous' 0 hw)

/-- The logarithm of a positive Gaussian density. -/
theorem log_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal 0 v x) =
      - Real.log (2 * Real.pi * v) / 2 - x ^ 2 / (2 * v) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp]
  simp only [sub_zero]
  ring

/-- The centered Gaussian log-density ratio is a quadratic polynomial. -/
theorem log_gaussianPDFReal_ratio {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0)
    (x : ℝ) :
    Real.log (gaussianPDFReal 0 v x / gaussianPDFReal 0 w x) =
      Real.log ((w : ℝ) / v) / 2 + x ^ 2 * (1 / w - 1 / v) / 2 := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw
  rw [Real.log_div (gaussianPDFReal_pos _ _ _ hv).ne'
      (gaussianPDFReal_pos _ _ _ hw).ne', log_gaussianPDFReal hv,
    log_gaussianPDFReal hw, Real.log_div hw' hv']
  rw [Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hv',
    Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hw']
  ring

/-- Gaussian log-likelihood ratios agree almost everywhere with their density ratios. -/
theorem llr_gaussianReal {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) :
    llr (gaussianReal 0 v) (gaussianReal 0 w) =ᵐ[gaussianReal 0 v]
      fun x => Real.log ((w : ℝ) / v) / 2 + x ^ 2 * (1 / w - 1 / v) / 2 := by
  have hRN := Measure.rnDeriv_withDensity_right (gaussianReal 0 v) volume
    (measurable_gaussianPDF 0 w).aemeasurable
    (ae_of_all _ fun x => (gaussianPDF_pos 0 hw x).ne')
    (ae_of_all _ fun _ => gaussianPDF_ne_top)
  rw [← gaussianReal_of_var_ne_zero 0 hw] at hRN
  filter_upwards [(gaussianReal_absolutelyContinuous 0 hv).ae_le hRN,
    (gaussianReal_absolutelyContinuous 0 hv).ae_le (rnDeriv_gaussianReal 0 v)] with x hx hxv
  rw [llr, hx, hxv, ENNReal.toReal_mul, ENNReal.toReal_inv,
    toReal_gaussianPDF, toReal_gaussianPDF]
  rw [mul_comm, ← div_eq_mul_inv, log_gaussianPDFReal_ratio hv hw]

/-- A centered real Gaussian has second moment equal to its variance. -/
theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_eq_integral (μ := gaussianReal 0 v) measurable_id.aemeasurable
  simpa using h.symm

/-- The Gaussian log-likelihood ratio has a finite first moment. -/
theorem integrable_llr_gaussianReal {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) :
    Integrable (llr (gaussianReal 0 v) (gaussianReal 0 w)) (gaussianReal 0 v) := by
  rw [integrable_congr (llr_gaussianReal hv hw)]
  exact (integrable_const _).add
    (((memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq.mul_const _).div_const 2)

/-- Relative entropy between centered real Gaussians in variance-ratio normalization. -/
theorem klDiv_gaussianReal {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) :
    klDiv (gaussianReal 0 v) (gaussianReal 0 w) =
      ENNReal.ofReal (((v : ℝ) / w - 1 - Real.log ((v : ℝ) / w)) / 2) := by
  rw [klDiv_of_ac_of_integrable (gaussianReal_absolutelyContinuous_gaussianReal hv hw)
    (integrable_llr_gaussianReal hv hw)]
  simp only [probReal_univ, add_sub_cancel_right]
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  rw [integral_congr_ae (llr_gaussianReal hv hw),
    integral_add (integrable_const _) ((hsq.mul_const _).div_const 2),
    integral_const, integral_div, integral_mul_const, integral_sq_gaussianReal]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  congr 1
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw
  rw [Real.log_div hw' hv', Real.log_div hv' hw']
  field_simp
  ring

/-- The scalar entropy remainder is quadratic when the variance ratio is at least one half. -/
theorem gaussian_entropy_remainder_le {t : ℝ} (ht : 1 / 2 ≤ t) :
    (t - 1 - Real.log t) / 2 ≤ (t - 1) ^ 2 := by
  have hpos : 0 < t := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have htinv : t * t⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hnonneg : 0 ≤ t - 1 - Real.log t :=
    sub_nonneg.mpr (Real.log_le_sub_one_of_pos hpos)
  have hproduct := mul_nonneg (sub_nonneg.mpr ht) hnonneg
  nlinarith

/-- Nearby positive real Gaussian variances have quadratically small relative entropy. -/
theorem klDiv_gaussianReal_le {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : 1 / 2 ≤ (v : ℝ) / w) :
    klDiv (gaussianReal 0 v) (gaussianReal 0 w) ≤
      ENNReal.ofReal (((v : ℝ) / w - 1) ^ 2) := by
  rw [klDiv_gaussianReal hv hw]
  exact ENNReal.ofReal_le_ofReal (gaussian_entropy_remainder_le hvw)

end Erdos522
